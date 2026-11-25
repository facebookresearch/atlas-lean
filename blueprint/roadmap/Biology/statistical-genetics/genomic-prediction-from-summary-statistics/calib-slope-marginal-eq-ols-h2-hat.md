# The PRS calibration slope is identified by LD-score regression

Let `μ` be a probability measure on `Ω`, let `(h², β, ε)` be an
[LD-score model](../ld-score-regression/model.md) on `μ` with `N ≠ 0` individuals and `M ≠ 0`
markers whose effects and noise have mean zero (`∫ β_k dμ = 0` and `∫ ε_i dμ = 0` for all `k` and
`i`), and let `X` be a [standardized](../ld-score-regression/is-standardized.md) real `N × M`
genotype matrix with [in-sample LD matrix](ld-matrix.md) `R` whose
[LD scores](../ld-score-regression/ld-score.md) `ℓ_1, …, ℓ_M` are not all equal. Let `ĥ²` be the
[unweighted LD-score regression estimator](../ld-score-regression/ols-h2-hat.md) applied to the LD
scores and the expected [association statistics](../ld-score-regression/chi-sq.md) `∫ χ²_j dμ`, and
let `β̂` be the [normalized marginal scores](../ld-score-regression/beta-hat.md). With target LD
matrix `R`, the [calibration slope](calib-slope.md) of the score `xᵀ β̂` is the
[calibration-slope formula](slope-formula.md) at `ĥ²`:

`(ĥ² L / M) / (ĥ² T / M + (1 - ĥ²) L / N)`,

where `L` is the [sum of the LD scores](ld-score-sum.md) and `T` the
[trace of the cube of the LD matrix](ld-cube.md), with the convention `x / 0 = 0`. It is thus a
function of summary-level quantities: the expected statistics, the LD scores, `tr R³`, `N` and `M`.
