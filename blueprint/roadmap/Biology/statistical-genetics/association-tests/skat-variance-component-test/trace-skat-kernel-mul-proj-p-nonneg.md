# With nonnegative weights tr(K P K Pᵀ) is nonnegative

If all variant weights are nonnegative, `wⱼ ≥ 0`, then for every real `n × q` covariate matrix `X`,
real `n × n` matrix `V` and real `n × m` genotype matrix `G`,

`tr(K P K Pᵀ) ≥ 0`,

with `K` the [SKAT kernel](skat-kernel.md) and `P` the [null projection](proj-p.md) built from `V`.
When `V` is positive definite and `Xᵀ V⁻¹ X` is invertible, it is the slope in `τ ≥ 0` of the
[mean of the SKAT statistic along the variance-component alternative](integral-skat-q-alt-cov.md).
