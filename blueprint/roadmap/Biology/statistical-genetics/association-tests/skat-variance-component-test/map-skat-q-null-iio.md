# Under the null the SKAT statistic is almost surely nonnegative

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where the inverse of a singular matrix is taken to be `0`, and let all variant weights
be nonnegative. Then for every `α ∈ ℝ^q` the law of the [SKAT statistic](skat-q.md) under
`y ~ N(X α, V)` gives the half-line `(-∞, 0)` measure `0`. Here the mean `X α` lies in the span of
the covariates, and `N(X α, V)` is the Gaussian law with mean `X α` and covariance `V` when `V` is
positive semidefinite, and the point mass at `X α` otherwise.
