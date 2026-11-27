# Rescaled lineage-count matrices converge to the Λ-coalescent generator

Under the [Möhle–Sagitov conditions](mohle-sagitov-lambda.md) (`c_N > 0` for all large `N`,
`c_N → 0`, `q_k / c_N → ∫ x^(k-2) Λ(dx)` for every `k ≥ 2`, and `D_N / c_N → 0`, with `q_k` the
probability that `k` sampled lineages share a parent and `D_N` that of a simultaneous double merger)
for a sequence of Cannings models and a finite measure `Λ` on `[0, 1]`, for every `n` the matrices
`c_N⁻¹ (Π_N - I)` converge entrywise, as `N → ∞`, to the
[block-counting generator](../../coalescents/block-counting-generator.md) `G_Λ` of the Λ-coalescent
on the states `0, …, n`, where `Π_N` is the one-generation
[transition matrix](../cannings-models/lineage-matrix.md) of the ancestral lineage count, `c_N` the
[coalescence probability](../cannings-models/coal-prob.md) and `I` the identity matrix. At an `N`
with `c_N = 0` (for instance `N ≤ 1`), `c_N⁻¹ = 0` and the rescaled matrix is the zero matrix; this
does not affect the limit.
