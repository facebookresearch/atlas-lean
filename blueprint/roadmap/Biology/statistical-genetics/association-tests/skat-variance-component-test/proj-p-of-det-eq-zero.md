# A singular covariance makes the null projection zero

If `det V = 0`, then for every real `n × q` covariate matrix `X` the [null projection](proj-p.md) is
`P = 0`, since with the convention that the inverse of a singular matrix is `0`, `V⁻¹ = 0`. Hence
the [SKAT statistic](skat-q.md) `Q = (P y)ᵀ K (P y)` is `0` for every `y`: the GLS formula that
defines the test has no inverse to use.
