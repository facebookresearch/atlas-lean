# Soundness error $2^{-m}$ over $m$ rounds

If $G_0$ and $G_1$ are not isomorphic, every adaptive cheating prover, whose graph and answer in each
round may depend on its coins and on the earlier challenges, passes all $m$ rounds of the
[graph-isomorphism protocol](sigma.md) with probability at most $2^{-m}$.

## Informally uses

- [Soundness error of sequential repetition](../zero-knowledge-proofs/soundness-error-of-sequential-repetition.md)
- [Special soundness of the graph-isomorphism protocol](sigma-special-sound.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, Protocol 2 and proof of Theorem 2.
