# The Bayes rule for two Gaussian laws is the matched-filter test

Let `ι` be a finite index set, `s₀, s₁ ∈ ℝ^ι`, `R` a positive definite `ι × ι` matrix, `π₀, π₁ > 0`,
and costs with `C₀₀ < C₁₀` and `C₁₁ < C₀₁`. With `p₀` and `p₁` the
[densities](../../distributions/continuous/multivariate-normal-distribution/gaussian-density/multivariate-gaussian-pdfreal.md)
of `N(s₀, R)` and `N(s₁, R)`, the finite-cost rule that decides `true` where
`π₀ (C₁₀ - C₀₀) p₀(y) < π₁ (C₀₁ - C₁₁) p₁(y)`, the tie decision where the two sides are equal and
`false` otherwise agrees at every observation `y`, including the tie branch, with the
[matched-filter rule](matched-filter-rule.md).
