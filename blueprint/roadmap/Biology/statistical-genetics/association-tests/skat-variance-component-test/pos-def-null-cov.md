# With residual noise the null covariance is positive definite

If `Φ` is a positive semidefinite real `n × n` matrix, possibly singular, `σ_g² ≥ 0` and `σ_e² > 0`,
then the [null covariance](null-cov.md) `Σ₀ = σ_g² Φ + σ_e² I` is positive definite. So a singular
relationship matrix is harmless when there is residual noise.
