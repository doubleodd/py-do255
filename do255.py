#! /usr/bin/env python3

# This is the reference implementation for groups do255e and do255s. It
# also includes functions for key exchange (ECDH), signature generation
# and verification (Schnorr signatures), and hash-to-curve.
#
# WARNING: This implementation is mathematically correct, but not secure
# as an implementation: it makes no effort at mitigating side-channel
# leaks (e.g. computation time). It is also not much optimized. The
# intended usage is production of test vectors, and exploration of
# addition formulas. Do NOT use it in production code.
#
# This file contains several classes and variables. In appearance order:
#
#   Zmod                     generic class for computing modulo a given integer
#
#   GF255e, GF255s           base fields for curve do255e and do255s
#
#   Scalar255e, Scalar255s   fields for scalars (integers modulo the group
#                            order, which is prime)
#
#   Do255Curve               base class for curve instances
#
#   Do255e, Do255s           instances for the two curves do255e and do255s
#
# All this code is meant for Python 3.4+.

# =========================================================================
# Custom implementation of modular integers.
#
# This mimics Sage syntax. For a modulus m, the ring of integers modulo
# m is defined as Zmod(m). A value is obtained by "calling" (function
# call syntax) the ring on an integer (or anything that can be
# transtyped into an integer); that integer is internally reduced.
# Values are immutable. When converted to a string or formatted, they
# behave like plain integers with a value in the 0..m-1 range.
#
# Inversion works only for an odd modulus. Square root extraction works
# only for a prime modulus equal to 3, 5 or 7 modulo 8 (i.e. an odd prime
# which is not equal to 1 modulo 8); if the modulus is not prime, then
# incorrect results will be returned.

class Zmod:
    def __init__(self, m):
        """
        Initialize for the provided modulus. The modulus must be convertible
        to a positive integer of value at least 2.
        """
        m = int(m)
        if m < 2:
            raise Exception('invalid modulus')
        self.m = m
        self.encodedLen = (m.bit_length() + 7) >> 3
        self.zero = Zmod.Element(self, 0)
        self.one = Zmod.Element(self, 1)
        self.minus_one = Zmod.Element(self, m - 1)

    def __call__(self, x):
        """
        Make a ring element. If x is already an element of this ring,
        then it is returned as is. Otherwise, x is converted to an integer,
        which is reduced modulo the ring modulus, and used to make a new
        value.
        """
        if isinstance(x, Zmod.Element) and (x.ring is self):
            return x
        return Zmod.Element(self, int(x) % self.m)

    def Decode(self, bb):
        """
        Decode an element from bytes (exactly the number of bytes matching
        the modulus length). Unsigned little-endian convention is used.
        If the value is not lower than the modulus, an exception is thrown.
        """
        if len(bb) != self.encodedLen:
            raise Exception('Invalid encoded value (wrong length = {0})'.format(len(bb)))
        x = int.from_bytes(bb, byteorder='little')
        if x >= self.m:
            raise Exception('Invalid encoded value (not lower than modulus)')
        return Zmod.Element(self, x)

    def DecodeReduce(self, bb):
        """
        Decode an element from bytes. All provided bytes are read, in
        unsigned little-endian convention; the value is then reduced
        modulo the ring modulus.
        """
        x = int.from_bytes(bb, byteorder='little')
        return Zmod.Element(self, x % self.m)

    class Element:
        def __init__(self, ring, value):
            self.ring = ring
            self.x = int(value)

        def __getattr__(self, name):
            if name == 'modulus':
                return self.ring.m
            else:
                raise AttributeError()

        def __int__(self):
            """
            Conversion to an integer returns the value in the 0..m-1 range.
            """
            return self.x

        def valueOfOther(self, b):
            if isinstance(b, Zmod.Element):
                if self.ring is b.ring:
                    return b.x
                if self.ring.m != b.ring.m:
                    raise Exception('ring mismatch')
                return b.x
            elif isinstance(b, int):
                return b % self.ring.m
            else:
                return False

        def __add__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(self.x + b)

        def __radd__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(b + self.x)

        def __sub__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(self.x - b)

        def __rsub__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(b - self.x)

        def __neg__(self):
            return self.ring(-self.x)

        def __mul__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(self.x * b)

        def __rmul__(self, b):
            b = self.valueOfOther(b)
            if b is False:
                return NotImplemented
            return self.ring(b * self.x)

        def __truediv__(self, y):
            # This function works only if the modulus is odd.
            # If the divisor is not invertible, then we return 0.
            #
            # We use a binary GCD. Invariants:
            #   a*x = u*y mod m
            #   b*x = v*y mod m
            # The GCD ends with b = 1, in which case v = x/y mod m.
            a = self.valueOfOther(y)
            if a is False:
                return NotImplemented
            m = self.ring.m
            if (m & 1) == 0:
                raise Exception('Unsupported division: even modulus')
            b = m
            u = self.x
            v = 0
            while a != 0:
                if (a & 1) == 0:
                    a >>= 1
                    if (u & 1) != 0:
                        u += m
                    u >>= 1
                else:
                    if a < b:
                        a, b = b, a
                        u, v = v, u
                    a -= b
                    if u < v:
                        u += m
                    u -= v
            # Note: if the divisor is zero, then we immediately arrive
            # here with v = 0, which is what we want.
            return self.ring(v)

        def __rtruediv__(self, y):
            return self.ring(y).__truediv__(self)

        def __floordiv__(self, y):
            return self.__truediv__(y)

        def __rfloordiv__(self, y):
            return self.ring(y).__truediv__(self)

        def __pow__(self, e):
            # We do not assume that the modulus is prime; therefore, we
            # cannot reduce the exponent modulo m-1.
            e = int(e)
            if e == 0:
                return self.ring.one
            t = self
            if e < 0:
                t = t.ring.one / t
                e = -e
            r = self
            elen = e.bit_length()
            for i in range(0, elen - 1):
                j = elen - 2 - i
                r *= r
                if ((e >> j) & 1) != 0:
                    r *= self
            return r

        def __lshift__(self, n):
            n = int(n)
            if n < 0:
                raise Exception('negative shift count')
            return self.ring(self.x << n)

        def __rshift__(self, n):
            n = int(n)
            if n < 0:
                raise Exception('negative shift count')
            m = self.ring.m
            if (m & 1) == 0:
                raise Exception('Unsupported right shift: even modulus')
            t = self.x
            while n > 0:
                if (t & 1) != 0:
                    t += m
                t >>= 1
                n -= 1
            return self.ring(t)

        def __eq__(self, b):
            if isinstance(b, Zmod.Element):
                if self.ring.m != b.ring.m:
                    return False
                return self.x == b.x
            else:
                return self.x == int(b)

        def __ne__(self, b):
            if isinstance(b, Zmod.Element):
                if self.ring.m != b.ring.m:
                    return True
                return self.x != b.x
            else:
                return self.x != int(b)

        def __repr__(self):
            return self.x.__repr__()

        def __str__(self):
            return self.x.__str__()

        def __format__(self, fspec):
            return self.x.__format__(fspec)

        def __bytes__(self):
            return self.x.to_bytes(self.ring.encodedLen, byteorder='little')

        def sqrt(self):
            """
            Compute a square root of the current value. If the value is
            not a square, this returns False. The returned square root is
            normalized: its least significant bit (as an integer in the
            0..m-1 range) is zero.

            WARNING: square root extraction assumes that the modulus is
            a prime integer. It works only for a modulus equal to 3, 5
            or 7 modulo 8.
            """
            m = self.ring.m
            if (m & 3) == 3:
                s = self**((m + 1) >> 2)
            elif (m & 7) == 5:
                # Atkin's formulas:
                #   b <- (2*a)^((m-5)/8)
                #   c <- 2*a*b^2
                #   return a*b*(c - 1)
                b = (self << 1)**((m - 5) >> 3)
                c = (self*b*b) << 1
                s = self*b*(c - 1)
            else:
                raise Exception('Unsupported square root for this modulus')
            if (s * s).x != self.x:
                return False
            if (s.x & 1) != 0:
                s = -s
            return s

        def is_zero(self):
            return self.x == 0

        def is_square(self):
            # This function works only if the modulus is odd.
            #
            # This is a Legendre/Jacobi symbol, that follows the same
            # reduction steps as a binary GCD.
            m = self.ring.m
            if (m & 1) == 0:
                raise Exception('Unsupported division: even modulus')
            a = self.x
            b = m
            if a == 0:
                return True
            ls = 1
            while a != 0:
                if (a & 1) == 0:
                    a >>= 1
                    if ((b + 2) & 7) > 4:
                        ls = -ls
                else:
                    if a < b:
                        a, b = b, a
                        if (a & b & 3) == 3:
                            ls = -ls
                    a -= b
            return ls == 1

# =========================================================================
# Concrete fields:
#
#   GF255e       field for do255e point coordinates; modulus m = 2^255 - 18651
#
#   Scalar255e   field for integers modulo the do255e group prime order:
#                r = 2^254 - 131528281291764213006042413802501683931
#
#   GF255s       field for do255e point coordinates; modulus m = 2^255 - 3957
#
#   Scalar255s   field for integers modulo the do255s group prime order:
#                r = 2^254 + 56904135270672826811114353017034461895

GF255e = Zmod(2**255 - 18651)
Scalar255e = Zmod(2**254 - 131528281291764213006042413802501683931)
GF255s = Zmod(2**255 - 3957)
Scalar255s = Zmod(2**254 + 56904135270672826811114353017034461895)

# =========================================================================
# Curves and points:
#
# An instance of Do255Curve represents one of the curves, or, more
# accurately, the prime order group defined out of the curve. Group
# elements ('points') are points on the curve that are part of that
# subgroup. Each point instance is immutable. A new point instance is
# obtained by calling an appropriate method on the Do255Curve instance,
# or by using the functions and operators on existing points.

class Do255Curve:
    def __init__(self, name):
        if name == 'do255e' or name == 'Do255e':
            name = 'Do255e'
            self.bname = b'do255e'
            self.K = GF255e
            self.SF = Scalar255e
            self.a = self.K(0)
            self.b = self.K(-2)
            self.eta = self.K(-1).sqrt()
            Gx = self.K(2)
            Gu = self.K(1)
        elif name == 'do255s' or name == 'Do255s':
            name = 'Do255s'
            self.bname = b'do255s'
            self.K = GF255s
            self.SF = Scalar255s
            self.a = self.K(-1)
            self.b = self.K(1)/2
            self.nonQR = self.K(-1)
            Gx = self.K(26116555989003923291153849381583511726884321626891190016751861153053671511729)
            Gu = self.K(3)
        else:
            raise Exception('Unknown curve: {0}'.format(name))
        self.name = name
        self.encodedLen = self.K.encodedLen
        self.N = Do255Curve.Point(self, self.K.zero, self.K.one, self.K.zero, self.K.one)
        self.G = Do255Curve.Point(self, Gx, self.K.one, Gu, self.K.one)
        self.alpha = (4*self.b - self.a**2) / (2*self.b - self.a)
        self.beta = (self.a - 2) / (2*self.b - self.a)

    def __call__(self, x, u):
        x = self.K(x)
        u = self.K(u)
        if x.is_zero() and u.is_zero():
            return self.N
        if x.is_zero() or u.is_zero():
            raise Exception('Invalid coordinates')
        if x != u*u*(x*(x + self.a) + self.b):
            raise Exception('Invalid coordinates')
        return Do255Curve.Point(self, x, self.K.one, u, self.K.one)

    def Decode(self, bb):
        """
        Decode 32 bytes (bb) into a point. This function enforces canonical
        representation. If the input consists of 32 zeros, then the decoded
        point is the group neutral N.
        """
        w = self.K.Decode(bb)
        if w.is_zero():
            return self.N
        t = w**2 - self.a
        d = t**2 - 4*self.b
        s = d.sqrt()
        if s is False:
            raise Exception('Invalid encoded point')
        x = (t + s) >> 1
        if x.is_square():
            x -= s
        # This verification should never fail.
        if (w**2)*x != x*(x + self.a) + self.b:
            raise Exception('Internal error: not a point')
        return Do255Curve.Point(self, x, self.K.one, self.K.one, w)

    def MapToCurve(self, bb):
        """
        Map a 32-byte input (bb) to a curve point. This map is not
        surjective and not uniform, but each output point can only have
        a limited number of antecedents, so that a proper hash-to-curve
        process can be built by generating 64 bytes from a hash
        function, mapping each half to a point, and adding the two
        points together.
        """
        # Decode input into a field element.
        e = self.K.DecodeReduce(bb)

        # We map to a point on the dual curve y^2 = x^3 - 2*a*x + (a^2-4*b)
        # so that get a point on the curve, then apply the isogeny:
        #   (x, u) -> (4*b*u^2, 2/(u*(x-b/x)))
        # to obtain a point in the proper group.
        #
        # Below, we denote aa = -2*a and bb = a^2 - 4*b. We must use
        # different methods, depending on whether a == 0 or a != 0.
        aa = -2*self.a
        bb = self.a**2 - 4*self.b

        if self.a.is_zero():
            # For curves with equation y^2 = x^3 + bb*x, we use the
            # following formulas, for input field element e:
            #   x1 = e + (1-bb)/(4*e)
            #   x2 = d*(e - (1-bb)/(4*e))
            # with d^2 = -1 mod p. Then at least one of x1, x2 and x1*x2
            # is a valid x coordinate for a curve point. We try them in
            # that order.
            #
            # To ensure interoperability, all implementation must use the
            # same conventions for square roots. We thus use computations
            # that correspond to what optimized code would do:
            #   yy1num = 64*e^7 + 16*(3+bb)*e^5 + 4*(3-2*bb-bb^2)*e^3 + (1-bb)^3*e
            #   yy2num = -d*(64*e^7 - 16*(3+bb)*e^5 + 4*(3-2*bb-bb^2)*e^3 - (1-bb)^3*e)
            # so that:
            #   x1^3 + bb*x1 = yy1num / (64*e^4)
            #   x2^3 + bb*x2 = yy2num / (64*e^4)
            # and the resulting point is one of:
            #     (x1, sqrt(yy1num)/(8*e^2))
            #     (x2, sqrt(yy2num)/(8*e^2))
            #     (x1*x2, sqrt(yy1num*yy2num)/(64*e^4))
            # The square root extraction (and "sign" normalization) is then
            # done on either yy1num, yy2num, or yy1num*yy2num.

            # 0 maps to N.
            if e.is_zero():
                return self.N

            d = self.eta
            x1num = 4*e**2 + (1-bb)
            x2num = d*(4*e**2 - (1-bb))
            x12den = 4*e

            yy1num = 64*e**7 + 16*(3+bb)*e**5 + 4*(3-2*bb-bb**2)*e**3 + (1-bb)**3*e
            yy2num = -d*(64*e**7 - 16*(3+bb)*e**5 + 4*(3-2*bb-bb**2)*e**3 - (1-bb)**3*e)
            y12den = 8*e**2

            if yy1num.is_square():
                xnum = x1num
                xden = x12den
                ynum = yy1num.sqrt()
                yden = y12den
            elif yy2num.is_square():
                xnum = x2num
                xden = x12den
                ynum = yy2num.sqrt()
                yden = y12den
            else:
                xnum = x1num*x2num
                xden = x12den**2
                ynum = (yy1num*yy2num).sqrt()
                yden = y12den**2

            # u = x/y
            X = xnum
            Z = xden
            U = xnum*yden
            T = xden*ynum

        else:
            # For curves y^2 = x^3 + aa*x^2 + bb*x with aa != 0, we use
            # the Elligator2 map:
            #   d = some non-square fixed value (e.g. d = -1 when p = 3 mod 4)
            #   if d*e^2 == -1:
            #       return N
            #   v = -aa/(1 + d*e^2)
            #   ls = Legendre(v*(v^2 + aa*v + bb))
            #   if ls == 1:
            #       x = v
            #   else:
            #       x = -v - aa
            #   y = ls*sqrt(x*(x^2 + aa*x + bb))
            #
            # To ensure interoperability, all implementation must use the
            # same conventions for square roots. We thus use computations
            # that correspond to what optimized code would do:
            #   yy1num = -aa*bb*d^3*e^6 + (aa^3-3*aa*bb)*d^2*e^4
            #            + (aa^3-3*aa*bb)*d*e^2 - aa*bb
            #   yy2num = -aa*bb*d^4*e^8 + (aa^3-3*aa*bb)*d^3*e^6
            #            + (aa^3-3*aa*bb)*d^2*e^4 - aa*bb*d*e^2
            #          = yy1num*d*e^2
            #   y12den = (1 + d*e^2)^4
            # If yy1num is a square, we use it; otherwise, we use yy2num.
            # The square root ynum is extracted and normalized (least
            # significant bit is set to zero); for the denominator,
            # we use: yden = (1 + d*e^2)^2

            d = self.nonQR
            Z = 1 + d*e**2
            if Z.is_zero():
                return self.N
            yy1num = -aa*bb*d**3*e**6 + (aa**3-3*aa*bb)*d**2*e**4 + (aa**3-3*aa*bb)*d*e**2 - aa*bb
            yy2num = yy1num*d*e**2
            if yy1num.is_square():
                X = -aa
                ynum = yy1num.sqrt()
            else:
                X = -aa*d*e**2
                ynum = -yy2num.sqrt()
            yden = Z**2

            # If e == 0, then we may get ynum == 0 here. In that case,
            # the point is N and we return it. Otherwise, the point is
            # not the neutral, and the subsequent computations won't fail.
            if ynum.is_zero():
                return self.N

            # u = x/y
            U = X*yden
            T = Z*ynum

        # Apply isogeny.
        #   x' = 4*b*u^2
        #   u' = 2*x/(u*(x^2 - bb))
        return Do255Curve.Point(self, 4*self.b*U**2, T**2, 2*X*Z*T, U*(X**2 - bb*Z**2))

    # Points internally use fractional (X:Z:U:T) coordinates, with:
    #    x == X/Z   u == U/T   Z != 0   T != 0
    class Point:
        def __init__(self, curve, X, Z, U, T):
            self.curve = curve
            self.X = X
            self.Z = Z
            self.U = U
            self.T = T

        def is_neutral(self):
            return self.U.is_zero()

        def coordinatesOfOther(self, other):
            if isinstance(other, Do255Curve.Point):
                if self.curve is other.curve:
                    return (other.X, other.Z, other.U, other.T)
            raise Exception('Curve mismatch')

        def __add__(self, other):
            X1, Z1, U1, T1 = self.X, self.Z, self.U, self.T
            X2, Z2, U2, T2 = self.coordinatesOfOther(other)
            a = self.curve.a
            b = self.curve.b
            alpha = self.curve.alpha
            beta = self.curve.beta
            t1 = X1*X2
            t2 = Z1*Z2
            t3 = U1*U2
            t4 = T1*T2
            t5 = (X1 + Z1)*(X2 + Z2) - t1 - t2
            t6 = (U1 + T1)*(U2 + T2) - t3 - t4
            t7 = t1 + b*t2
            t8 = t4*t7
            t9 = t3*(2*b*t5 + a*t7)
            t10 = (t4 + alpha*t3)*(t5 + t7)
            X3 = b*(t10 - t8 + beta*t9)
            Z3 = t8 - t9
            U3 = -t6*(t1 - b*t2)
            T3 = t8 + t9
            return Do255Curve.Point(self.curve, X3, Z3, U3, T3)

        def __neg__(self):
            return Do255Curve.Point(self.curve, self.X, self.Z, -self.U, self.T)

        def __sub__(self, other):
            return self + (-other)

        def __mul__(self, n):
            # Make sure the scalar is in the proper field of scalars. This
            # ensures modular reduction if the source value is an integer.
            if isinstance(n, Zmod.Element) and (n.ring is self.curve.SF):
                n = int(n)
            else:
                n = int(self.curve.SF(n))

            # Simple double-and-add algorithm. In this implementation,
            # we aim for clarity, not performance or mitigation of side
            # channels.
            if n == 0:
                return self.curve.N
            P = self
            nlen = n.bit_length()
            for i in range(0, nlen - 1):
                j = nlen - 2 - i
                P += P
                if ((n >> j) & 1) != 0:
                    P += self
            return P

        def __rmul__(self, n):
            return self * n

        def __eq__(self, other):
            X1, Z1, U1, T1 = self.X, self.Z, self.U, self.T
            X2, Z2, U2, T2 = self.coordinatesOfOther(other)
            return U1*T2 == U2*T1

        def __ne__(self, other):
            X1, Z1, U1, T1 = self.X, self.Z, self.U, self.T
            X2, Z2, U2, T2 = self.coordinatesOfOther(other)
            return U1*T2 != U2*T1

        # This function inverts two values with the cost of only one
        # internal inversion, and three multiplications. However, if
        # either value is non-invertible, then both results will be zero.
        def invx2(a, b):
            c = a*b
            d = 1 / c
            return (b*d, a*d)

        def xu(self):
            iZ, iT = Do255Curve.Point.invx2(self.Z, self.T)
            return (self.X * iZ, self.U * iT)

        def xw(self):
            # If the point is the neutral, self.U == 0 and both iZ
            # and iU are set to 0, which is fine for us because we
            # want to return (0, 0) in that case.
            iZ, iU = Do255Curve.Point.invx2(self.Z, self.U)
            return (self.X * iZ, self.T * iU)

        def xy(self):
            x, w = self.xw()
            return (x, w*x)

        def __getattr__(self, name):
            if name == 'x':
                return self.X / self.Z
            elif name == 'u':
                return self.U / self.T
            elif name == 'w':
                # division returns 0 if divisor is 0
                return self.T / self.U
            elif name == 'y':
                # division returns 0 if divisor is 0
                return (self.X * self.T) / (self.Z * self.U)

        def __repr__(self):
            x, u = self.xu()
            return '{0}({1}, {2})'.format(self.curve.name, x, u)

        def __bytes__(self):
            return bytes(self.w)

# =========================================================================
# Concrete curves:
#
#   Do255e    equation y^2 = x*(x^2 - 2) in field GF(2^255-18651)
#   Do255s    equation y^2 = x*(x^2 - x + 1/2) in field GF(2^255-3957)

Do255e = Do255Curve('do255e')
Do255s = Do255Curve('do255s')

# =========================================================================
# High-level cryptographic algorithms.
#
# We define key exchange (ECDH) and signatures (Schnorr) on top of
# both do255e and do255s.
#
# Noteworthy details:
#
#  - A private key is an integer in the 1..r-1 range. A private key is
#    encoded over 32 bytes. When decoding, all bits are taken into
#    account (no ignored bit). Out-of-range values are rejected when
#    decoding. Note that 0 is not a valid private key.
#
#  - A public key is a point. It encodes into 32 bytes. When decoding, all
#    bits are taken into account (no ignored bit). Canonical encoding is
#    enforced: a given curve point can be validly encoded in only one way.
#    The group neutral (N, encoded as a sequence of bytes of value 0x00)
#    is not a valid public key; such a value MUST be rejected if
#    encountered when decoding.
#
#  - An ECDH message is a public key. It follows the rules of public keys,
#    as stated above. Thus, it cannot be a neutral point.
#
#  - A signature is the concatenation of a point (32 bytes) and a scalar
#    value (32 bytes). They follow the same rules as public and private
#    keys described above, except that the neutral point is allowed as
#    first signature half, and the value zero is allowed as second
#    signature half. Out of range values and non-canonical encodings of
#    points MUST still be rejected, and there is no ignored bit.
#
#  - Since the group has prime order, there is no ambiguousness about
#    the signature verification equation.

import hashlib
import os

def Keygen(curve, sh = None):
    """
    Generate a new keypair. If sh is provided, then it must be a SHAKE256
    context pre-fed with a seed; the key pair is then deterministically
    generated from that context. If sh is not provided (or is None), then
    the OS-provided random generator (os.urandom()) is used.

    Returned value is the private key (as a scalar instance).
    """
    if sh == None:
        sh = hashlib.shake_256()
        sh.update(os.urandom(32))
    j = 0
    while True:
        # We use a loop on the off-chance that we get a value which is
        # zero modulo r. This is extremely improbable and nobody knows
        # how to initialize a SHAKE256 context so that it outputs such
        # a value.
        #
        # We only extract 32 bytes (256 bits) at a time, because the
        # group order (on both do255e and do255s) is close enough to
        # 2^254 that the modulo reduction induces no statistically
        # detectable bias.
        bb = sh.digest(curve.encodedLen * (j + 1))
        sk = curve.SF.DecodeReduce(bb[curve.encodedLen * j:])
        if not sk.is_zero():
            return sk
	j += 1

def EncodePrivate(sk):
    """
    Encode a private key into bytes (exactly 32 bytes for both
    do255e and do255s).
    """
    return bytes(sk)

def DecodePrivate(curve, bb):
    """
    Decode a private key from bytes. Note that the length must match the
    expected value (32 bytes for both do255e and do255s) and the value
    is verified to be in the proper range (1 to r-1, with r being the
    prime order of the do255* group).
    """
    sk = curve.SF.Decode(bb)
    if sk.is_zero():
        raise Exception('Invalid private key (zero)')
    return sk

def MakePublic(curve, sk):
    """
    Make a public key (curve point) out of a private key.
    """
    return curve.G * sk

def EncodePublic(pk):
    """
    Encode a public key into bytes.
    """
    return bytes(pk)

def DecodePublic(curve, bb):
    """
    Decode a public key from bytes. Invalid points are rejected. The
    neutral element is NOT accepted as a public key.
    """
    pk = curve.Decode(bb)
    if pk.is_neutral():
        raise Exception('Invalid public key (neutral point)')
    return pk

def ECDH(sk, pk, peer_pk, secret_len):
    """
    Do an ECDH key exchange. sk is our private key; pk is the matching
    public key (normally generated from sk with makePublic()). peer_pk
    is the public key received from the peer. secret_len is the length,
    in bytes, of the shared secret to generate (internally, SHAKE256 is
    used for key derivation, so that length can be arbitrary).

    peer_pk may be either a decoded point (from decodePublic()), or
    directly the received bytes (as an array of bytes or a 'bytes' object).
    If peer_pk is a decoded point, then the process cannot fail (unless
    that point is not on the same curve as our public key).

    If peer_pk is provided in encoded format (as bytes), then this
    function decodes it internally. Decoding failures then trigger the
    alternate key derivation: the ecdh() function does not fail, but
    instead generates a secret key in a way which is deterministic from
    the exchanged public values, and our private key. External attackers
    cannot distinguish between a success or a failure; this is meant for
    some (rare) protocols in which exchanged points are masked, and
    outsiders shall not be able to find out whether a given sequence of
    bytes is the masked value of a proper point or not.

    Returned value are:
       (ok, key)
    with:
       ok    boolean, True for success, False for failure
       key   the generated secret, of length 'secret_len' bytes
    """
    curve = pk.curve
    enc_peer_pk = bytes(peer_pk)
    peer_pk_good = True
    if not(isinstance(peer_pk, Do255Curve.Point)):
        try:
            peer_pk = pk.curve.Decode(enc_peer_pk)
            if peer_pk.is_neutral():
                raise Exception('key is neutral')
        except Exception:
            # If using the "alternate key on failure" feature, then we
            # should still compute a point multiplication, to avoid
            # leaking the information about the failure through timing.
            # Of course, this specific implementation is not constant-time
            # anyway, so it may still leak that way. We still mimic the
            # behaviour that a secure implementation would have.
            peer_pk_good = False
            peer_pk = curve.G
    else:
        if not(pk.curve is peer_pk.curve):
            raise Exception('Curve mismatch in ECDH')

    # The ECDH core: multiply the peer point by our private key.
    # The shared secret is the _square_ of the w coordinate of the result
    # (a square is used to make ECDH implementable with a ladder
    # algorithm that avoids full decoding of the input point).
    sharedPoint = peer_pk * sk
    shared = sharedPoint.w**2

    # For key generation, we want to use SHAKE256 over the concatenation of:
    #   - a domain separation string (that includes the curve name);
    #   - a byte that specifies success or failure;
    #   - the shared secret (our private key on failure);
    #   - the two public keys
    # We order the public keys by interpreting them as integers
    # (little-endian convention) so that both parties use the same order.
    pk1 = bytes(pk.w)
    ipk1 = int(pk.w)
    pk2 = enc_peer_pk
    ipk2 = int.from_bytes(pk2, byteorder='little')
    if ipk1 > ipk2:
        pk1, pk2 = pk2, pk1
    sh = hashlib.shake_256()
    sh.update(curve.bname)
    sh.update(b'-ecdh:')
    if peer_pk_good:
        sh.update(b'\x00')
        sh.update(bytes(shared))
    else:
        sh.update(b'\xFF')
        sh.update(bytes(sk))
    sh.update(bytes(pk1))
    sh.update(bytes(pk2))
    return (peer_pk_good, sh.digest(secret_len))

# Internal function used in signature generation and verification: it
# computes the "challenge" as the hash of the concatenation of:
#   - a domain separation string (that includes the curve name);
#   - the R point (first half of the signature);
#   - the public key (pk);
#   - the identifier of the hash function used to process the data
#     (decimal-dotted OID, or an empty string for unhashed data,
#     followed by a colon character);
#   - the (hashed) data.
# Hash function is SHAKE256. Output is a sequence of bytes matching the
# size of the encoding of a scalar on that curve; the bytes are interpreted
# as an integer in little-endian unsigned convention, and reduced modulo
# the scalar modulus (r): this is the "challenge" value, which is returned.
def make_e(R, pk, hash_oid, hv):
    curve = pk.curve
    sh = hashlib.shake_256()
    sh.update(curve.bname)
    sh.update(b'-sign-e:')
    sh.update(bytes(R))
    sh.update(bytes(pk))
    sh.update(hash_oid)
    sh.update(b':')
    sh.update(hv)
    return curve.SF.DecodeReduce(sh.digest(curve.SF.encodedLen))

# Hash function identifier strings for some standard hash functions.
OID_SHA224      = b'2.16.840.1.101.3.4.2.4'
OID_SHA256      = b'2.16.840.1.101.3.4.2.1'
OID_SHA384      = b'2.16.840.1.101.3.4.2.2'
OID_SHA512      = b'2.16.840.1.101.3.4.2.3'
OID_SHA512_224  = b'2.16.840.1.101.3.4.2.5'
OID_SHA512_256  = b'2.16.840.1.101.3.4.2.6'
OID_SHA3_224    = b'2.16.840.1.101.3.4.2.7'
OID_SHA3_256    = b'2.16.840.1.101.3.4.2.8'
OID_SHA3_384    = b'2.16.840.1.101.3.4.2.9'
OID_SHA3_512    = b'2.16.840.1.101.3.4.2.10'

def Sign(sk, pk, hash_oid, hv, seed = b''):
    """
    Sign the provided (hashed) data 'hv'. The signer's private (sk) and
    public (pk) keys are used. The data is assumed to have been hashed
    with the hash function identified by 'hash_oid' (decimal-dotted
    notation for the hash object identifier, as a binary string);
    if the unhashed raw data is provided as 'hv', then 'hash_oid' should
    be set to the empty string b''.

    Using raw data makes the signature engine resilient to collision
    attacks on hash functions, but it also makes streamed processing
    harder for memory-constrained systems. Using a collision-resistant
    hash function (e.g. SHA-3) is recommended.

    The 'seed' is an optional binary string that can augment the internal
    generation of the per-secret signature. Without a seed, deterministic
    generation is used, which is safe. An extra non-constant seed value
    (which needs not be random) makes signatures randomized; it can also
    provide some extra resilience against fault attacks (of course, if
    fault attacks are an issue, then side channels are also an issue,
    and this reference implementation shall not be used).
    """
    curve = pk.curve

    # Make the per-signature k value. We use SHAKE256 over an encoding
    # of a domain separation string, the private key, the seed, and the
    # data (with its hash identifier), and reduce the output modulo r.
    # Note that we don't need to get more bytes than the size of r
    # because the value of r is very close to a power of two in both
    # do255e and do255s (in both case, it is 2^254 + r0 for a signed
    # integer r0 such that |r0| < 2^127), making the bias negligible.
    sh = hashlib.shake_256()
    sh.update(curve.bname)
    sh.update(b'-sign-k:')
    sh.update(bytes(sk))
    sh.update(len(seed).to_bytes(8, 'little'))
    sh.update(seed)
    sh.update(hash_oid)
    sh.update(b':')
    sh.update(hv)
    k = curve.SF.DecodeReduce(sh.digest(curve.SF.encodedLen))

    # Use the per-signature secret scalar k to generate the signature.
    R = curve.G * k
    e = make_e(R, pk, hash_oid, hv)
    s = k + e*sk
    return bytes(R) + bytes(s)

def Verify(pk, sig, hash_oid, hv):
    """
    Verify the signature 'sig' (bytes) over the provided (hashed) data
    'hv' (hashed with the function identified by 'hash_oid'; use the
    empty string b'' if data is unhashed) against the public key pk.
    Returned value is True on success (signature is valid for this
    public key and that data), False otherwise.
    """
    try:
        curve = pk.curve
        clen = curve.encodedLen
        if len(sig) != (clen << 1):
            return False
        R = curve.Decode(sig[:clen])
        s = curve.SF.Decode(sig[clen:])
        e = make_e(R, pk, hash_oid, hv)
        return curve.G*s - pk*e == R
    except Exception:
        return False

def HashToCurve(curve, hash_oid, hv):
    """
    Hash the provided input data into a curve point. The data (hv) is
    either raw unhashed data, or a hash value if the data was pre-hashed.
    'hash_oid' identifies the hash function used for pre-hashing; use b''
    (empty string) for raw unhashed data. Returned point can be any point
    on the group, including the neutral N.
    """
    n = curve.K.encodedLen
    sh = hashlib.shake_256()
    sh.update(curve.bname)
    sh.update(b'-hash-to-curve:')
    sh.update(hash_oid)
    sh.update(b':')
    sh.update(hv)
    blob = sh.digest(2 * n)
    return curve.MapToCurve(blob[:n]) + curve.MapToCurve(blob[n:])
