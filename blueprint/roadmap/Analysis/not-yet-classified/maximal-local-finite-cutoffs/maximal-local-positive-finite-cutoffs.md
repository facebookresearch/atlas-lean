# Positive finite cutoffs with projection and order bounds

Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a
positive bounded complex-linear functional for the spectral orders. Let `S` be the
constructed maximal set of pairwise orthogonal nonzero star projections, each admitting a
vector `ξ` with `Re ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`.
`maximalLocalPositiveFiniteCutoffs M ψ` returns `t ↦ P_t`, each a star projection
satisfying `0≤P_t≤I`, `‖P_t‖≤1`; the map is monotone and its range is nonempty and
directed.
