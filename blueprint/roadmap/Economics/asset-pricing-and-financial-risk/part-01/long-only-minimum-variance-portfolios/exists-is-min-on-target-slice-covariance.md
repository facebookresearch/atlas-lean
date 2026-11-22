# Long-only minimum variance is attained

Let `R_i` be square-integrable returns of finitely many assets on a probability space, with
expectations `μ_i = E[R_i]`, and let `m` be a target return. If some weight vector `w` satisfies
`w_i ≥ 0` for every `i`, `∑_i w_i = 1` and `∑_i μ_i w_i = m`, then the covariance quadratic form
`∑_{i,j} w_i w_j Cov(R_i, R_j)` attains its minimum on the set of such weight vectors.

This is the same statement as
[Long-only minimum variance is attained (restated)](exists-is-min-on-cov-matrix-target-slice.md).
Here the variance is written with the matrix of covariances `Cov(R_i, R_j)` spelled out; the linked
page writes it as `wᵀ C w` with the covariance matrix `C` of the returns.
