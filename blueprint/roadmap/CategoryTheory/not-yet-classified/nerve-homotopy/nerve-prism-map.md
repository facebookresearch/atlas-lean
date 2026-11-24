# Nerve Prism Map

The prism `nerve C ⊗ Δ[n] ⟶ nerve D` determined by a functor
`Φ : C × Fin (n + 1) ⥤ D`: at a pair `(s, t)` it is `Φ` applied to the
composable arrows `s` paired with the simplex `t` of `Δ[n]` read as a
functor into `Fin (n + 1)`. For `n = 1` and `Φ` the cylinder functor
of a natural transformation this is
`CategoryTheory.NatTrans.nerveHomotopyMap`, by definition.
