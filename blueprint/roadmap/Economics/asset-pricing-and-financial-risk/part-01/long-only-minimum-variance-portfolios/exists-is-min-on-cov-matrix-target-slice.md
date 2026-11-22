# Long-only minimum variance is attained (restated)

Let `R_i` be square-integrable returns of finitely many assets on a probability space, with
covariance matrix `C` (`C_ij = Cov(R_i, R_j)`) and expected returns `μ_i = E[R_i]`, and let `m`
be a target return. If the long-only target-return slice (weight vectors `w` with `w_i ≥ 0` for
every `i`, `∑_i w_i = 1` and `∑_i μ_i w_i = m`) is nonempty, then `wᵀ C w` attains its minimum
on it.

This is the same statement as
[Long-only minimum variance is attained](exists-is-min-on-target-slice-covariance.md). Here the
variance is written as `wᵀ C w` with the covariance matrix `C` of the returns; the linked page
spells out the matrix of covariances `Cov(R_i, R_j)`.
