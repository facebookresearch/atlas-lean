# Normal functional of a finite projection localization sum

Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a
positive bounded complex-linear functional for the spectral orders. Let `p_i ∈ M` be star
projections indexed by an arbitrary type `I`, and `ξ_i ∈ H` satisfy `Re ψ(b)≤Re
⟨ξ_i,bξ_i⟩` whenever `0≤b≤p_i`. for `s : Finset I`, `finiteLocalizedNormalFunctional`
returns `ρ_s∈M_*` with `ρ_s(a)=ψ(a*Σ_i∈s p_i)` for all `a∈M`. No pairwise orthogonality is
assumed.
