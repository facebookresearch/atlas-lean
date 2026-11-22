# Variance of a two-asset portfolio

For returns `R₁` and `R₂` on a measure space and a weight `w ∈ ℝ`, the variance of the two-asset
portfolio with weight `w` on `R₁` and `1 - w` on `R₂` is `Var(w R₁ + (1 - w) R₂)`, where
`Var(X) = ∫ (X - E[X])² dμ` and `E[X] = ∫ X dμ`, with the conventions that the integral of a
non-integrable function is `0` and an infinite variance is `0`. The budget constraint is built in
(`w + (1 - w) = 1`); short sales are allowed: `w` ranges over all of `ℝ`.
