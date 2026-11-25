# The shrinkage error is orthogonal to the marginal scores

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) on a measure `μ` with `N`
individuals and `M` markers, and let `X` be a real `N × M` genotype matrix whose
[second-moment matrix of the marginal scores](score-cov.md) `V` is invertible (`det V ≠ 0`). Then
for all markers `k, l`, the error of the [shrunk estimate](blup-score.md) `β̃_k` is orthogonal in
`L²(μ)` to the [normalized marginal score](../ld-score-regression/beta-hat.md) `β̂_l`:

`∫ (β_k - β̃_k) β̂_l dμ = 0`.
