# Spectral decomposition of a symmetric stress

Let `σ` be a real [symmetric](is-symmetric-stress.md) `3 × 3` matrix, let `u₀, u₁, u₂` be the
orthonormal basis of eigenvectors chosen by the spectral theorem, with eigenvalues `λ₀, λ₁, λ₂` (the
[principal stresses](principal-stresses-real.md)), and let `U` be the matrix with columns
`u₀, u₁, u₂`. Then `U` is orthogonal, `Uᵀ U = U Uᵀ = 1`, and `σ = U diag(λ₀, λ₁, λ₂) Uᵀ`, that is
`σ = ∑_j λ_j u_j u_jᵀ`. The basis is a choice and is not unique: each `u_j` can be replaced by
`-u_j`, and a repeated principal stress allows any orthonormal basis of its eigenspace.
