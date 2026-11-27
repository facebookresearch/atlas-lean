# Representing vector for a projection-localized positive functional

Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M →
ℂ` be a positive bounded complex-linear functional for the spectral orders. Let `p ∈ M` be
a star projection and `ξ ∈ H` satisfy `Re ψ(b)≤Re ⟨ξ,bξ⟩` for every positive `b≤p`.
`localizedFunctionalVector M ψ p ξ` returns `η∈H` satisfying `ψ(ap)=⟨η,(ap)ξ⟩` for every
`a∈M`. The input vector need not satisfy `pξ=ξ`.
