# Solution of Hutchinson's delayed logistic equation

For real numbers `r`, `K` and `τ` and functions `φ, x : ℝ → ℝ`, `x` solves Hutchinson's delayed
logistic equation `x'(t) = r x(t) (1 - x(t - τ) / K)` with history `φ` when `x = φ` on `[-τ, 0]`,
`x` is continuous on `[-τ, ∞)`, and at every `t ≥ 0` the right derivative of `x` is
`r x(t) (1 - x(t - τ) / K)`. The definition is total: with the convention `a / 0 = 0`, for `K = 0`
the equation reads `x'(t) = r x(t)`; for `τ < 0` the history interval `[-τ, 0]` is empty and the
delayed term looks ahead. The intended domain is `τ ≥ 0`. In the model the growth rate `r` and the
carrying capacity `K` are positive and `x` is a population size.
