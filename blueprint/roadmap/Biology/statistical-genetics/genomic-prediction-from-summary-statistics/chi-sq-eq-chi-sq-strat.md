# The association statistic is the stratified one with zero shift

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) with `N` individuals and
`M` markers, and let `X` be a real `N × M` genotype matrix. For every `c ∈ ℝ^N` and every marker
`j`, the [association statistic](../ld-score-regression/chi-sq.md) `χ²_j` equals, pointwise on `Ω`,
the [association statistic under stratification](../ld-score-regression/chi-sq-strat.md) with shift
`s = 0` along `c`.
