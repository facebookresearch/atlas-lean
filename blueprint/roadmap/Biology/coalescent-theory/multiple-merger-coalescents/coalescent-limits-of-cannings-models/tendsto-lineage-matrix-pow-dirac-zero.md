# With limit measure δ₀ the lineage count converges to Kingman's

When a sequence of Cannings models satisfies the [Möhle–Sagitov conditions](mohle-sagitov-lambda.md)
(`c_N > 0` for all large `N`, `c_N → 0`, `q_k / c_N → ∫ x^(k-2) Λ(dx)` for every `k ≥ 2`, and
`D_N / c_N → 0`, with `q_k` the probability that `k` sampled lineages share a parent and `D_N` that
of a simultaneous double merger) with `Λ = δ₀` (no heavy tail), for every `n` and `t ≥ 0`,
`Π_N^⌊t / c_N⌋ → exp(t G_K)` as `N → ∞`, where `Π_N` is the one-generation
[transition matrix](../cannings-models/lineage-matrix.md) of the ancestral lineage count on
`0, …, n`, `c_N` the [coalescence probability](../cannings-models/coal-prob.md) and `G_K`
[Kingman's pure-death generator](../../ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md)
on `0, …, n` (`k → k - 1` at rate `C(k, 2)`): the time-rescaled lineage count converges to Kingman's
block-counting process. At an `N` with `c_N = 0` (for instance `N ≤ 1`), `t / c_N = 0`, so
`⌊t / c_N⌋ = 0` and the matrix power is the identity; this does not affect the limit.
