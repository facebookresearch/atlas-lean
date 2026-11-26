# Tensor comparison agrees with successive and direct restriction

Let `(C,J,ℛ)` be a commutative ringed site at universe `u`, `h : V → U`, with weak additive
sheafification, monoidal `W`, and locally-bijective and underlying-ring comparisons on the
base and both slices. For ambient module sheaves `M,N`, write `F_U,F_V` for base restrictions,
`F_h` for restriction along `h`, `γ_A : F_h(F_U A) ≅ F_V A` for `overFunctorMap`, and
`δ_U,δ_V,δ_h` for the tensor comparisons. Then `γ_{M⊗N}.hom ≫ δ_V(M,N).hom = F_h(δ_U(M,N).hom)
≫ δ_h(F_U M,F_U N).hom ≫ (γ_M.hom ⊗ γ_N.hom)`.
