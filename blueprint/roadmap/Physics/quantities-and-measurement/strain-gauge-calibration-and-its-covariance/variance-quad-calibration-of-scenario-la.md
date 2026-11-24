# Variance quad Calibration of scenario Law

Output covariance under a finite scenario law entirely in `[a, b]` (nonnegative weights of
total mass one), with Taylor base `v₀ ∈ [a, b]`: the output variance keeps the remainder
variance and the linear/remainder cross term,
`Var f(V) = f' v₀ ^ 2 Var V + c2 ^ 2 Var (V - v₀) ^ 2 + 2 f' v₀ c2 Cov(V, (V - v₀) ^ 2)`,
while the Hessian theorem bounds the remainder only pointwise, scenario by scenario.
