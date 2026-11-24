# Shrunk marginal effect estimates

Let `(h², β, ε)` be an [LD-score model](../ld-score-regression/model.md) with `N` individuals and
`M` markers, and let `X` be a real `N × M` genotype matrix. The shrunk effect estimates are the
functions

`β̃_k = ∑_n K_kn β̂_n`

on `Ω`, that is `β̃ = K β̂`, where `K` is the [shrinkage matrix](shrink-matrix.md) built from `h²`
and `X` and `β̂` are the [normalized marginal scores](../ld-score-regression/beta-hat.md). When the
[second-moment matrix of the marginal scores](score-cov.md) is singular, `K = 0` and so `β̃ = 0`.
