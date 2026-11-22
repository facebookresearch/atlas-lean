# Systematic plus idiosyncratic variance decomposition (FI07.T03)

For an
orthogonal single-index residual (`cov[RM, ε; μ] = 0`), the variance of the
single-index return splits as `Var[R_i; μ] = β ^ 2 * Var[RM; μ] + Var[ε; μ]`.
The constant `α` drops out, the cross term vanishes by orthogonality, and the
`β ^ 2` factor comes from `variance_const_mul`. The cited Mathlib lemmas
(`variance_add`, `variance_const_mul`, `covariance_const_mul_left`) are not
reproved.
