# Minimum-variance weight formula for two assets

For returns `R₁` and `R₂` with variances `σ₁²`, `σ₂²` and covariance `σ₁₂` under a measure `μ`,
the two-asset minimum-variance weight is `w* = (σ₂² - σ₁₂) / Var(R₁ - R₂)`, with the convention
`x / 0 = 0` (so `w* = 0` when `Var(R₁ - R₂) = 0`). It is unconstrained in `w ∈ ℝ`, the budget
constraint being built into the `(w, 1 - w)` parametrization. For square-integrable returns
under a finite measure the denominator is `Var(R₁ - R₂) = σ₁² - 2σ₁₂ + σ₂²`.
