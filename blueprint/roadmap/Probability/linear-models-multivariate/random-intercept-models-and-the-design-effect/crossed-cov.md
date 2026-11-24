# Diagonal covariance of crossed random intercepts

For index types `I` and `J` and real numbers `σ_s²` and `σ_w²`, the crossed random-effects
covariance is the diagonal matrix on `I ⊔ J` with entry `σ_s²` at each row index `i ∈ I` and `σ_w²`
at each column index `j ∈ J`. It is the covariance intended for the random effects of the
[crossed design](crossed-design.md): variance `σ_s²` for each row effect, `σ_w²` for each column
effect, and no covariance between distinct effects. No sign is imposed on `σ_s²` and `σ_w²`; the
matrix is [positive semidefinite](pos-semidef-crossed-cov.md) when both are nonnegative.
