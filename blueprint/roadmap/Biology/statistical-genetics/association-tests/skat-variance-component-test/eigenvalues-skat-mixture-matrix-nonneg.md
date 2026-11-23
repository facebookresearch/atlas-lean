# With nonnegative variant weights the mixture weights are nonnegative

If all variant weights are nonnegative, `wⱼ ≥ 0`, then for all `X`, `V`, `G` and every real `n × n`
matrix `V'`, every eigenvalue of the symmetric [mixture matrix](skat-mixture-matrix.md)
`A = (P V'^{1/2})ᵀ K (P V'^{1/2})` is nonnegative. When `Xᵀ V⁻¹ X` is invertible these eigenvalues
are the weights of the [law of the SKAT statistic](map-skat-q-multivariate-gaussian.md) under
`y ~ N(X α, V')`.
