# Möhle–Sagitov: convergence of a Cannings model to the Λ-coalescent

Under the
Möhle–Sagitov conditions, for every `t ≥ 0` the `⌊t / c_N⌋`-generation transition matrix of the
ancestral lineage count of a sample of at most `n` converges, as `N → ∞`, to the time-`t`
transition matrix `exp (t • G_Λ)` of the Λ-coalescent's block-counting process, with
`G_Λ = LambdaCoalescent.blockCountingGenerator Λ n` and Λ the measure whose moments are the
limits `lim q_k / c_N` of the offspring factorial moments.

## Sources

- M. Möhle, S. Sagitov, *A classification of coalescent processes for haploid exchangeable population models*, Ann. Probab. 29 (2001), Theorem 2.1 (Λ case: Sagitov 1999). Only the block-counting process (number of ancestral lineages) and convergence of the finite-dimensional transition matrices are covered; the partition-valued process and path-space (Skorokhod) convergence are not.
