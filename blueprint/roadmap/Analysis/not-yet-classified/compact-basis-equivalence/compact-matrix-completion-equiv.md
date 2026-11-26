# Star equivalence between completed basis matrices and compacts

Let `H` be a complex
normed inner-product space with a Hilbert basis `b : HilbertBasis ℕ ℂ H`; this basis
implies completeness. Let `D=lim_n M_(n+1)(ℂ)` be the algebraic direct limit along
top-left zero padding, with norm `‖[n,X]‖=‖X‖`. Put `C=Completion D`, with the extended
C-star norm, and `Φ : C → K(H)` the extension of `[n,X] ↦ Σ_i,j<n+1 X_ij θ_(b_i,b_j)`,
where `θ_(x,y)z=⟨y,z⟩x`. `compactMatrixCompletionEquiv b : C ≃⋆ₐ[ℂ] K(H)` is the
star-algebra equivalence whose forward map is `Φ`, the norm-preserving completed
matrix-corner embedding.
