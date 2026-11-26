# Straight-line extraction for VOLE-in-the-head in the random oracle model

For the all-but-one vector commitment with leaves hashed by a random oracle (one repetition, $2^d$ leaves), there is a straight-line extractor that reads the random-oracle query log, recovers the committed leaf seeds and hence the prover's witness from any accepted proof, except with probability bounded by the number of leaf-hash queries times $2^{-\lambda}$ plus the soundness error of the VOLE proof. If instead leaf commitments are computed locally with a PRG (as in AES-CTR leaf hashing), no such straight-line extractor exists in the plain random oracle model: there are two statements with disjoint witness sets and a valid proof whose query log is consistent with both.

## Proof sketch

Every opened leaf must be the image of a logged query unless the adversary guessed an oracle output; the hidden leaf's seed is determined by inverting the logged commitment. With PRG-based leaves the commitment is computed without oracle queries, so the log carries no information about the seed.

## Depends on

- [VOLE-in-the-head](vole-in-the-head.md)
- [The random oracle model](../../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [VOLE-based zero-knowledge proofs for arithmetic circuits](../../zero-knowledge-and-arguments/vole-zero-knowledge/vole-circuit-zero-knowledge.md)

## Sources

- Carsten Baum et al., "Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from VOLE-in-the-Head", Advances in Cryptology – CRYPTO 2023, Part V, 2023.
- Carsten Baum et al., "Shorter, Tighter, FAESTer: Optimizations and Improved (QROM) Analysis for VOLE-in-the-Head Signatures", Cryptology ePrint Archive, Paper 2026/164, 2026.
