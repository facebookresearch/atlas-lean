# The mixture weights sum to tr(K P V' Pᵀ)

If `V'` is a positive semidefinite real `n × n` matrix, then for all `X`, `V`, `G` and `w` the
eigenvalues `λ₁, …, λₙ`, listed with multiplicity, of the [mixture matrix](skat-mixture-matrix.md)
`A = (P V'^{1/2})ᵀ K (P V'^{1/2})` satisfy

`∑ⱼ λⱼ = tr(K P V' Pᵀ)`,

with `P` the [null projection](proj-p.md) built from `V` and `K` the [SKAT kernel](skat-kernel.md).
