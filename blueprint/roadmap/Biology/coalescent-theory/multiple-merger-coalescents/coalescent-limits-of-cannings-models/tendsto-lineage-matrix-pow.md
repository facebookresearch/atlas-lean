# Möhle–Sagitov limit of the lineage count of Cannings models

Under the [Möhle–Sagitov conditions](mohle-sagitov-lambda.md) (`c_N > 0` for all large `N`,
`c_N → 0`, `q_k / c_N → ∫ x^(k-2) Λ(dx)` for every `k ≥ 2`, and `D_N / c_N → 0`, with `q_k` the
probability that `k` sampled lineages share a parent and `D_N` that of a simultaneous double merger)
for a sequence of Cannings models and a finite measure `Λ` on `[0, 1]`, for every `n` and every
`t ≥ 0` the `⌊t / c_N⌋`-generation transition matrix `Π_N^⌊t / c_N⌋` of the ancestral lineage count
of a sample of at most `n` converges, as `N → ∞`, to the time-`t` transition matrix `exp(t G_Λ)` of
the Λ-coalescent's block-counting process, where `Π_N` is the one-generation
[transition matrix](../cannings-models/lineage-matrix.md) on `0, …, n`, `G_Λ` the
[block-counting generator](../../coalescents/block-counting-generator.md) on `0, …, n`, and `Λ` the
measure whose moments `∫ x^(k-2) Λ(dx)`, for integers `k ≥ 2`, are the limits of `q_k / c_N`; here
`c_N` is the [coalescence probability](../cannings-models/coal-prob.md), `q_k` the
[probability](../cannings-models/merge-prob.md) that `k` sampled lineages share a parent, and `⌊y⌋`
the largest natural number at most `y`. At an `N` with `c_N = 0` (for instance `N ≤ 1`),
`t / c_N = 0`, so `⌊t / c_N⌋ = 0` and the matrix power is the identity; this does not affect the
limit. Only the block-counting process and its transition matrices at fixed times are concerned; the
partition-valued process and path-space (Skorokhod) convergence are not.

## Sources

- M. Möhle, S. Sagitov, *A classification of coalescent processes for haploid exchangeable
  population models*, Ann. Probab. 29 (2001), Theorem 2.1 (Λ case: Sagitov 1999).
