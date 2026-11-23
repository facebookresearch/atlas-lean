# For invertible Xᵀ V⁻¹ X, covariates drop out of the kernel statistic

Let `X` be a real `n × q` covariate matrix and `V`, `K` real `n × n` matrices such that `Xᵀ V⁻¹ X`
is invertible, where `V⁻¹` is the inverse of `V`, or `0` when `V` is singular (with at least one
covariate, the invertibility of `Xᵀ V⁻¹ X` forces `V` to be invertible). Then the
[kernel score statistic](kernel-q.md) `Q_K(y) = (P y)ᵀ K (P y)` ignores covariate effects:

`Q_K(X α + y) = Q_K(y)` for every `α ∈ ℝ^q` and `y ∈ ℝⁿ`,

because the null projection `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` satisfies `P X = 0`.
