# Shrinkage matrix for the marginal scores

For natural numbers `N`, `M`, a real number `h²` and a real `N × M` genotype matrix `X` with
[in-sample LD matrix](ld-matrix.md) `R`, the shrinkage matrix is the real `M × M` matrix

`K = (h² / M) R V⁻¹`,

where `V` is the [second-moment matrix of the marginal scores](score-cov.md), with the convention
that the inverse of a singular matrix is the zero matrix: `K = 0` when `V` is singular. In an
[LD-score model](../ld-score-regression/model.md) with heritability `h²` on a measure `μ`, and when
`V` is invertible, `K β̂` is the best linear predictor (without intercept) in `L²(μ)` of the effects
`β` from the [normalized marginal scores](../ld-score-regression/beta-hat.md) `β̂`: the error is
orthogonal to every score
([the shrinkage error is orthogonal to the marginal scores](integral-sub-blup-score-mul-beta-hat.md)).
