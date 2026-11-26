# Computational universal hash function

A keyed hash family $H$ with a secret uniform key is a *computational universal hash function* if every efficient adversary, given the security parameter but not the key, outputs two distinct valid messages $m \ne m'$ with $H_k(m) = H_k(m')$ only with negligible probability. It is *multi-query* secure if this holds for adversaries outputting a list of $Q$ messages and winning when some distinct pair in the list collides.

## Depends on

- [Universal hash family](../../../data-structures/hashing/universal-hashing/is-universal.md)
- [Negligible functions](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/negligible.md)

## Sources

- M. Bellare, "New Proofs for NMAC and HMAC: Security without Collision-Resistance", Journal of Cryptology 28(4), 2015 (definition of computationally almost universal (cAU) function families and the au-advantage).
