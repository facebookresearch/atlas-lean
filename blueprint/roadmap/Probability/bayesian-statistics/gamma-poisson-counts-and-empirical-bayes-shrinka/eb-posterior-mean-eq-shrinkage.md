# The empirical-Bayes posterior mean as a shrinkage combination

For `s > 0`, `0 < M < V` and `k ∈ ℕ`, the [empirical-Bayes posterior mean](eb-posterior-mean.md) is
`w · (k / s) + (1 − w) · (M / s)` with `w = s / (b̂ + s)` and `b̂ = s M / (V − M)`: a convex
combination of the per-cell estimate `k / s` and the plug-in prior mean `â / b̂ = M / s`.
