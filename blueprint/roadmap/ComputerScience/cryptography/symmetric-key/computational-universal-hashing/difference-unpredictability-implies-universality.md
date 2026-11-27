# Computational difference unpredictability implies computational universal hashing

Every computationally difference-unpredictable hash family is a computational universal hash function, with equal advantage: a collision adversary outputting $(m, m')$ becomes a difference adversary outputting $(m, m', 0)$.

## Proof sketch

A collision is exactly a difference prediction with $\delta = 0$; the encoding of zero is the same at every modulus.

## Depends on

- [Computational difference unpredictability](computational-difference-unpredictability.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
