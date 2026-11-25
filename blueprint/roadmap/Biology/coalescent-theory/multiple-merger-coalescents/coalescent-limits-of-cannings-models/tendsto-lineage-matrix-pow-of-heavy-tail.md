# Heavy-tailed Cannings lineage counts have a multiple-merger limit

Under the [Möhle–Sagitov conditions](mohle-sagitov-lambda.md) (`c_N > 0` for all large `N`,
`c_N → 0`, `q_k / c_N → ∫ x^(k-2) Λ(dx)` for every `k ≥ 2`, and `D_N / c_N → 0`, with `q_k` the
probability that `k` sampled lineages share a parent and `D_N` that of a simultaneous double merger)
for a sequence of Cannings models and a finite measure `Λ` on `[0, 1]`, together with the
[heavy-tail condition](heavy-tailed.md) (`q_3 / c_N` has a positive limit), for every `n` and
`t ≥ 0`: `Λ ≠ δ₀`, the triple-merger rate `λ_{3,3} = ∫ x Λ(dx)` is positive, and
`Π_N^⌊t / c_N⌋ → exp(t G_Λ)` as `N → ∞`, where `Π_N` is the one-generation
[transition matrix](../cannings-models/lineage-matrix.md) of the ancestral lineage count on
`0, …, n`, `c_N` the [coalescence probability](../cannings-models/coal-prob.md) and `G_Λ` the
[block-counting generator](../../coalescents/block-counting-generator.md) of the Λ-coalescent: the
time-rescaled ancestral lineage count converges to the Λ-coalescent's block-counting process
([convergence theorem](tendsto-lineage-matrix-pow.md)). At an `N` with `c_N = 0` (for instance
`N ≤ 1`), `t / c_N = 0`, so `⌊t / c_N⌋ = 0` and the matrix power is the identity; this does not
affect the limit.
