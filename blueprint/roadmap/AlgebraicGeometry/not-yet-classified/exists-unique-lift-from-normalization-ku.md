# Local universal property of a normalized Kummer cover

Let `X` be a normal integral scheme with function field `K`, `V` a nonempty affine open, `k` a
natural number invertible on `V`, `h ≠ 0` an element of `K`, and `u` a unit on `V` whose germ
at every point of `V` maps to `g / h ^ k` in `K`. Let `Y` be the normalization of `X` in
`Spec K[t]/(t ^ k - g)`, with structure map `π : Y ⟶ X`, and let `ρ` be the class of `t`.
Take a section `T` of `Y` over `π ⁻¹ᵁ V` whose pullback along `Spec K[t]/(t ^ k - g) ⟶ Y` is
the restriction of `h⁻¹ * ρ`: the root normalized so that its `k`-th power is `g / h ^ k`, the
image of `u`, and not `g`. Then a morphism `z : Z ⟶ X` with `z ⁻¹ᵁ V = ⊤`, together with a
global section `τ` of `Z` whose restriction to `z ⁻¹ᵁ V` has `k`-th power `z.app V u`, lifts to
a unique `s : Z ⟶ Y` with `s ≫ π = z` such that `s.app (π ⁻¹ᵁ V) T` is the restriction of
`τ`.
