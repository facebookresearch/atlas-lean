# Extraction from the VOLEHash consistency check

In VOLE-in-the-head with $\tau$ repetitions, the prover must show that the $u$ vectors of all repetitions are consistent by sending a universal hash of them under a verifier challenge (the KOS-style consistency check). There is an affine-line extractor which, given the prover's responses for several challenges, recovers a consistent witness unless a *bad pair* or *bad triple* of responses occurs; by the universality of the hash family, a bad pair occurs with probability at most the collision probability of the hash times the number of pairs, and on the complement the extractor's output is correct. This bounds the soundness loss of the VOLE-in-the-head compilation by a term linear in the number of random-oracle queries divided by $2^\lambda$.

## Proof sketch

If no bad configuration occurs, any three responses determine an affine line through the consistent witness; a bad configuration requires a hash collision among responses to distinct challenges.

## Depends on

- [VOLE-in-the-head](vole-in-the-head.md)
- [Universal hash family](../../../../data-structures/hashing/universal-hashing/is-universal.md)

## Sources

- Carsten Baum et al., "FAEST v3: Algorithm Specifications", FAEST Team, 2026.
