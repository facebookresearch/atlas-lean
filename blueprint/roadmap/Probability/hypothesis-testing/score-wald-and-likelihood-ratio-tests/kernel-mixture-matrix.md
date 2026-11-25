# Mixture-weight matrix of a kernel score statistic

For a real `n × q` covariate matrix `X` and real `n × n` matrices `V`, `K` and `V'`, the
mixture-weight matrix is

`A = (P V'^{1/2})ᵀ K (P V'^{1/2})`,

where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the
[null projection](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/proj-p.md) built from `V`, the inverse of a
singular matrix being taken to be `0`, and `V'^{1/2}` is the positive semidefinite square root of
`V'` when `V'` is positive semidefinite and `0` otherwise, in which case `A = 0`. For a symmetric
kernel `K` the matrix `A` is [symmetric](is-hermitian-kernel-mixture-matrix.md). If moreover
`Xᵀ V⁻¹ X` is invertible, the eigenvalues of `A` are the weights of the
[chi-square mixture law](map-kernel-q-multivariate-gaussian.md) of the
[kernel score statistic](kernel-q.md) `Q_K(y)` when `y` has law `N(X α, V')`, for every `α`; for a
positive semidefinite `V'` this is the Gaussian law with mean `X α` and covariance `V'`, and for any
other `V'` it is the point mass at `X α`, where `Q_K = 0`, matching `A = 0`. Under the null model
`V' = V`.
