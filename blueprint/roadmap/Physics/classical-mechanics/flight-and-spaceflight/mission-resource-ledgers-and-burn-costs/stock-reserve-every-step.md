# Deducting the reserve at every step removes it t times

For real reserves `r : ι → ℝ` (of any sign), initial stocks `s₀`, flows `flow`, a resource `i` and
`t ∈ ℕ`, the [stock](stock.md) with the flows `flow j k − r j` is `stock(i, t) − t r i`. For `t ≥ 2`
and `r i ≠ 0` it differs from the stock with the initial stocks `s₀ − r` and the original flows, the
single deduction.
