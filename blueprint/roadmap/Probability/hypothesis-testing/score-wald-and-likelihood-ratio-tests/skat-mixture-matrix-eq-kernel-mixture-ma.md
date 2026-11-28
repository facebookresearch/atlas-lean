# The SKAT mixture matrix is the mixture matrix of the SKAT kernel

For a real `n × q` covariate matrix `X`, real `n × n` matrices `V` and `V'`, a real `n × m` genotype
matrix `G` and variant weights `w ∈ ℝᵐ`, the
[SKAT mixture matrix](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/skat-mixture-matrix.md) is the
[mixture-weight matrix](kernel-mixture-matrix.md) of the SKAT kernel `K = G diag(w) Gᵀ`: both are

`(P V'^{1/2})ᵀ G diag(w) Gᵀ (P V'^{1/2})`,

where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection, the inverse of a singular
matrix being taken to be `0`, and `V'^{1/2}` is the positive semidefinite square root of `V'` when
`V'` is positive semidefinite and `0` otherwise.
