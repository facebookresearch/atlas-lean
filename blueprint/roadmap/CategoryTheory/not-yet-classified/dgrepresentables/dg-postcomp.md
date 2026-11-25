# Postcomposition

**Postcomposition** with a morphism `u : X ⟶ X'` of degree `n`, as a degree-`n` morphism
`Hom(Y, X) ⟶ Hom(Y, X')` of the DG category of cochain complexes between the values at `Y` of the
representable modules of `X` and `X'`, linear in `u`.  It is precomposition with `u` in the
opposite DG category, so its component on morphisms of degree `p` sends `g` to the Keller-ordered
composite `u ∘ g = (-1) ^ (p * n) • (g ≫ u)` (`MathlibExt.DGSource.dgPostcomp_v`).
