# With limit measure δ₀ the lineage count converges to Kingman's

When a sequence of Cannings models satisfies the
[Möhle–Sagitov conditions](mohle-sagitov-lambda.md) with `Λ = δ₀` (no heavy tail), for every `n`
and `t ≥ 0`, `Π_N^⌊t / c_N⌋ → exp(t G_K)` as `N → ∞`, where `Π_N` is the one-generation
[transition matrix](../cannings-models/lineage-matrix.md) of the ancestral lineage count on
`0, …, n`, `c_N` the [coalescence probability](../cannings-models/coal-prob.md) and `G_K`
[Kingman's pure-death generator](../../ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md)
on `0, …, n` (`k → k - 1` at rate `C(k, 2)`): the time-rescaled lineage count converges to
Kingman's block-counting process.
