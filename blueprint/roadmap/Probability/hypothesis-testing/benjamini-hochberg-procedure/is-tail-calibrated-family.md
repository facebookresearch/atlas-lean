# Tail-calibrated family of association tests

Let `μ` be a measure on `Ω`, `T i : Ω → ℝ` and `G i : ℝ → ℝ` the statistics and reference upper
tails of `m` tests, `i = 0, …, m - 1`, and `H0 ⊆ {0, …, m - 1}` the set of true nulls. The family
is tail-calibrated with true nulls `H0` when every statistic `T i` is measurable, every reference
tail `G i` is nonincreasing, and for every `i ∈ H0` the reference tail dominates the tail of
`T i`: `μ{ω : s ≤ T i ω} ≤ max(G i s, 0)` for every real `s` (so `μ{s ≤ T i} = 0` where
`G i s < 0`). The [p-values](tail-pvalue.md) `G i (T i ω)` of such a family are
[measurable](measurable-tail-pvalue.md), and those of the null genes are
[valid](is-valid-pvalue.md). For example, burden and SKAT-type tests with a conservative reference
null, and genomic-control tests whose inflation factor removes all of the inflation, have this
form.
