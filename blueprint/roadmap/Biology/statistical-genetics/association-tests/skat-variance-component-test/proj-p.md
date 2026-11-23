# Null projection matrix of the SKAT test

For a real `n × q` covariate matrix `X` and a real `n × n` matrix `V`, the null projection is the
`n × n` matrix

`P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`,

with the convention that the inverse of a singular matrix is `0`. So `P = 0` when `V` is singular,
and `P = V⁻¹` when `V` is invertible but `Xᵀ V⁻¹ X` is singular. The intended use has `V` and
`Xᵀ V⁻¹ X` invertible, for example `V` positive definite and `X` of full column rank. When
`Xᵀ V⁻¹ X` is invertible, [`P X = 0`](proj-p-mul-self.md); when moreover `V` is positive definite,
[`P V P = P`](proj-p-mul-mul-proj-p.md).
