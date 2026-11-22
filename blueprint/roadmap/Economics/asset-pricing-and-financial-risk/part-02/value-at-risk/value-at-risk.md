# Value at risk at level α

For a loss law `μ` on `ℝ` with distribution function `F` (`F(x) = μ((-∞, x])` when `μ` is a
probability measure) and a level `α ∈ (0, 1)`, the value at risk is the lower `α`-quantile of
the loss law, the value at `α` of its
[quantile function](../../../../Probability/distributions/distribution-functions/quantile-function-and-inverse-transform-sampling/quantile-function/cdf-quantile.md):
`VaR_α = inf {x ∈ ℝ : α ≤ F(x)}`. For `α ∉ (0, 1)` it is set to `0`.
