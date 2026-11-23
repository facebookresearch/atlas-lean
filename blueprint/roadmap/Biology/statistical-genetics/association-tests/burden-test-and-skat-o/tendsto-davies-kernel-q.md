# Davies' integral for a kernel statistic converges to its mid-p tail

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where `V⁻¹` is the inverse of `V`, or `0` when `V` is singular. Let `K` be a symmetric
real `n × n` kernel, `α ∈ ℝ^q`, `V'` any real `n × n` matrix and `c` a real number. Let
`λ₁, …, λₙ` be the eigenvalues of the [mixture-weight matrix](kernel-mixture-matrix.md)
`(P V'^{1/2})ᵀ K (P V'^{1/2})`, where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null
projection, and let `φ(t) = ∏ⱼ (1 - 2 i λⱼ t)^{-1/2}` (principal branch; each base has real part
`1`), the characteristic function of `∑ⱼ λⱼ χ²₁`. Then, as `T → ∞`,

`1/2 + π⁻¹ ∫₀^T Im(e^{-i t c} φ(t)) / t dt → (ℙ(Q_K > c) + ℙ(Q_K ≥ c)) / 2`,

the mid-p upper tail at `c` of the [kernel score statistic](kernel-q.md) `Q_K(y) = (P y)ᵀ K (P y)`,
with `ℙ` the probability under which `y` has law `N(X α, V')`. Here `N(X α, V')` is the image of the
standard Gaussian law on `ℝⁿ` under `z ↦ X α + V'^{1/2} z`: when `V'` is positive semidefinite,
`V'^{1/2}` is its positive semidefinite square root and `N(X α, V')` is the Gaussian law with mean
`X α` and covariance `V'`; for any other `V'`, `V'^{1/2}` is taken to be `0` and `N(X α, V')` is
the point mass at `X α`. The result applies to SKAT, the burden test and every SKAT-O statistic
through their symmetric kernels (Davies 1980, eq. (1), stated for the upper tail).
