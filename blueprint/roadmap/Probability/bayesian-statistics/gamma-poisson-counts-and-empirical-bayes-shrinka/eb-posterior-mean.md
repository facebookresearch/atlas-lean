# Empirical-Bayes posterior mean

For real numbers `s`, `M`, `V` and `k ∈ ℕ`, the empirical-Bayes posterior mean is
`(â + k) / (b̂ + s)`: the [posterior mean](posterior-mean.md) with the hyperparameters replaced by
the moment estimates `â = M² / (V − M)` and `b̂ = s M / (V − M)` from a count mean `M` and variance
`V`, with the convention `x / 0 = 0` in each quotient. The intended domain is `s > 0` and
`0 < M < V`.
