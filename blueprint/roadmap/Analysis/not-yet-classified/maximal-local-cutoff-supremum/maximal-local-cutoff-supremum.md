# Positive least upper bound of the finite cutoff family

Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive
bounded complex-linear functional for the spectral orders. Let `S` be the constructed
maximal set of pairwise orthogonal nonzero star projections, each admitting a vector `ξ`
with `Re ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`.
`maximalLocalCutoffSupremum M ψ` returns `s∈M₊` that is the least upper bound of `{P_t}`,
with `‖s‖≤1` and `s≤I_M`.
