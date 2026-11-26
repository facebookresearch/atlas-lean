# Goldreich–Micali–Wigderson: zero-knowledge proofs for NP from one-way functions

If one-way functions secure against nonuniform adversaries exist, then every language in NP, and every NP relation with its native witnesses, has an auxiliary-input zero-knowledge interactive proof with an efficient prover, perfect completeness, and negligible soundness error.

## Proof sketch

Nonuniform one-way functions give nonuniform pseudorandom generators and hence Naor commitments with nonuniform hiding. Commitments yield a zero-knowledge proof for an NP-complete relation (graph 3-colorability) with constant soundness error; sequential repetition makes the error negligible, and Levin reductions transfer the proof to every NP relation.

## Depends on

- [Auxiliary-input computational zero knowledge](auxiliary-input-zero-knowledge.md)
- [The complexity class NP](../../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)
- [One-way function families](../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Nonuniform one-way functions yield nonuniform pseudorandom generators](../../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/pseudoentropy-pairs-and-holenstein-construction/nonuniform-one-way-functions-yield-nonuniform-prgs.md)
- [Naor's commitment is computationally hiding and statistically binding](naor-commitment-security.md)
- [Zero knowledge of the graph 3-coloring protocol](../../zero-knowledge-and-arguments/zero-knowledge-of-the-graph-3-coloring-protocol.md)
- [Soundness of the graph 3-coloring protocol](../../zero-knowledge-and-arguments/soundness-of-the-graph-3-coloring-protocol.md)
- [Sequential repetition gives negligible soundness while preserving zero knowledge](zero-knowledge-soundness-amplification.md)
- [Zero knowledge transfers along Levin reductions](zero-knowledge-via-levin-reductions.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that Yield Nothing but Their Validity or All Languages in NP Have Zero-Knowledge Proof Systems", Journal of the ACM 38(3), 1991.
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
