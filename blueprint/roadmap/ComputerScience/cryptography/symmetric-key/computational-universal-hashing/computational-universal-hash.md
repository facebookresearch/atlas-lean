# Computational universal hash function

A keyed hash family $H$ (with public setup and a secret uniform key) is a *computational universal hash function* if every efficient adversary, given the security parameter and the public setup but not the key, outputs two distinct valid messages $m \ne m'$ with $H_k(m) = H_k(m')$ only with negligible probability. It is *multi-query* secure if this holds for adversaries outputting a list of $Q$ messages and winning when some distinct pair in the list collides.

## Depends on

- [Universal hash family](../../../data-structures/hashing/universal-hashing/is-universal.md)
- [Negligible functions](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/negligible.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
