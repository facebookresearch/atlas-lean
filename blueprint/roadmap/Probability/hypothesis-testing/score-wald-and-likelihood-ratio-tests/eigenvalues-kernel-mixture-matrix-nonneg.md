# A positive semidefinite kernel gives nonnegative mixture weights

Let `X` be a real `n × q` covariate matrix and `V`, `K`, `V'` real `n × n` matrices. If `K` is
positive semidefinite (symmetric, with `xᵀ K x ≥ 0` for every `x ∈ ℝⁿ`), then every eigenvalue of
the [mixture-weight matrix](kernel-mixture-matrix.md) `A = (P V'^{1/2})ᵀ K (P V'^{1/2})` is
nonnegative, for every `V'`: `A` is itself positive semidefinite. Here
`P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection, the inverse of a singular matrix
being taken to be `0`, and `V'^{1/2}` is the positive semidefinite square root of `V'` when `V'` is
positive semidefinite and `0` otherwise, which makes `A = 0`.
