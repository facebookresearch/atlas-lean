# Values and inverse laws of the completed basis compact equivalence

Let `H` be a
complex normed inner-product space with a Hilbert basis `b : HilbertBasis ℕ ℂ H`; this
basis implies completeness. Let `D=lim_n M_(n+1)(ℂ)` be the algebraic direct limit along
top-left zero padding, with norm `‖[n,X]‖=‖X‖`. Put `C=Completion D`, with the extended
C-star norm, and `Φ : C → K(H)` the extension of `[n,X] ↦ Σ_i,j<n+1 X_ij θ_(b_i,b_j)`,
where `θ_(x,y)z=⟨y,z⟩x`. for `e=compactMatrixCompletionEquiv b`, all three identities
hold: `e(x)=Φ(x)` and `e⁻¹(Φ(x))=x` for `x ∈ C`, and `Φ(e⁻¹(T))=T` for `T ∈ K(H)`.
