# Second moments of the marginal scores under LD

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with `N`
individuals and `M` markers, and let `X` be a real `N × M` genotype matrix with
[in-sample LD matrix](ld-matrix.md) `R`. Then for all markers `j, l` the
[normalized marginal scores](../ld-score-regression/beta-hat.md) satisfy

`∫ β̂_j β̂_l dμ = (h² / M) (R²)_jl + ((1 - h²) / N) R_jl`,

the entries of the [second-moment matrix of the marginal scores](score-cov.md), with the convention
`x / 0 = 0` (both sides are `0` when `N = 0`).
