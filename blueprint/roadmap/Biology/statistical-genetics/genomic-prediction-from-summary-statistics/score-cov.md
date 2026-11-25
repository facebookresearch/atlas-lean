# Second-moment matrix of the marginal scores

For natural numbers `N`, `M`, a real number `h²` and a real `N × M` genotype matrix `X` with
[in-sample LD matrix](ld-matrix.md) `R`, define the real `M × M` matrix

`V = (h² / M) R² + ((1 - h²) / N) R`,

with the convention `x / 0 = 0` (`V = 0` when `N = 0`, since then `R = 0`). In an
[LD-score model](../ld-score-regression/model.md) with heritability `h²` on a measure `μ`, `V` is
the matrix of raw second moments `∫ β̂_j β̂_l dμ` of the
[normalized marginal scores](../ld-score-regression/beta-hat.md)
([second moments of the marginal scores under LD](integral-beta-hat-mul-beta-hat.md)); it is their
covariance matrix when `μ` is a probability measure and the scores have mean zero.
