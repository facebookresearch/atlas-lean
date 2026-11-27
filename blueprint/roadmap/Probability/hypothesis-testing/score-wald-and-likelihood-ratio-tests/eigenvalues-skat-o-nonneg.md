# For 0 ≤ ρ ≤ 1 the SKAT-O mixture weights are nonnegative

Let `X` be a real `n × q` covariate matrix, `V` and `V'` real `n × n` matrices, `G` a real `n × m`
genotype matrix, `a ∈ ℝᵐ` variant weights and `ρ` a real number with `0 ≤ ρ ≤ 1`. Then every
eigenvalue of `(P V'^{1/2})ᵀ K_ρ (P V'^{1/2})` is nonnegative, where `K_ρ` is the
[SKAT-O kernel](skat-okernel.md), [positive semidefinite](pos-semidef-skat-okernel.md) for these
`ρ`, and `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection, the inverse of a singular
matrix being taken to be `0`; `V'^{1/2}` is the positive semidefinite square root of `V'` when `V'`
is positive semidefinite, and `0` otherwise. When `Xᵀ V⁻¹ X` is invertible, these eigenvalues are
the weights of the [chi-square mixture law](map-skat-oq-multivariate-gaussian.md) of the SKAT-O
statistic `Q_ρ` under `y ~ N(X α, V')`, the Gaussian law with mean `X α` and covariance `V'` when
`V'` is positive semidefinite and the point mass at `X α` otherwise (then every weight is `0`).
