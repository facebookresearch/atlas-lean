# The two-asset minimum-variance weight is a global minimizer

For square-integrable returns `R₁` and `R₂` under a finite measure with `Var(R₁ - R₂) > 0`, the
weight `w* = (σ₂² - σ₁₂) / Var(R₁ - R₂)`, where `σ₂² = Var(R₂)` and `σ₁₂ = Cov(R₁, R₂)`,
minimizes the two-asset portfolio variance `Var(w R₁ + (1 - w) R₂)` over all `w ∈ ℝ`. The budget
constraint is built into the `(w, 1 - w)` parametrization; no target-return constraint is
imposed; `w*` need not lie in `[0, 1]`.
