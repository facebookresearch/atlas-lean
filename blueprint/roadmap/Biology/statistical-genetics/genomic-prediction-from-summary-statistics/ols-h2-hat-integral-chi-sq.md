# LD-score regression identifies h² from the expected statistics

Let `μ` be a probability measure on `Ω`, let `(h², β, ε)` be an
[LD-score model](../ld-score-regression/model.md) on `μ` with `N ≠ 0` individuals and `M ≠ 0`
markers whose effects and noise have mean zero (`∫ β_k dμ = 0` and `∫ ε_i dμ = 0` for all `k` and
`i`), and let `X` be a [standardized](../ld-score-regression/is-standardized.md) real `N × M`
genotype matrix with [in-sample LD matrix](ld-matrix.md) `R` whose
[LD scores](../ld-score-regression/ld-score.md) `ℓ_1, …, ℓ_M` are not all equal. Then the
[unweighted LD-score regression estimator](../ld-score-regression/ols-h2-hat.md), applied to the LD
scores and the expected [association statistics](../ld-score-regression/chi-sq.md) `∫ χ²_j dμ`,
returns `h²`. This is the case without stratification of the
[population consistency of the unweighted estimator](../ld-score-regression/ols-h2-hat-integral-chi-sq-strat.md).
The expected statistics are affine in the LD scores with slope `N h² / M`, by
[LD-score regression](../ld-score-regression/integral-chi-sq-of-standardized.md):
`∫ χ²_j dμ = N h² ℓ_j / M + 1 - h²`.
