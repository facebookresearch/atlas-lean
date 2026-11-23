# The mixture matrix of a symmetric kernel is symmetric

Let `X` be a real `n × q` covariate matrix and `V`, `K`, `V'` real `n × n` matrices. If the kernel
is symmetric, `Kᵀ = K`, then the [mixture-weight matrix](kernel-mixture-matrix.md)
`A = (P V'^{1/2})ᵀ K (P V'^{1/2})` is symmetric for every `V'`, so its eigenvalues are real. Here
`P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection, the inverse of a singular matrix
being taken to be `0`, and `V'^{1/2}` is the positive semidefinite square root of `V'` when `V'` is
positive semidefinite and `0` otherwise.
