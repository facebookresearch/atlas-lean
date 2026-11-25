# Unreduced result at modulus one

For every natural number $a$, modular exponentiation with
base $a$, exponent $0$ and modulus $1$ returns $1$, whereas $a^0 \bmod 1 = 0$.

The base case of the CLRS procedure returns $1$ without reducing it modulo the modulus; this
boundary case keeps that visible.
