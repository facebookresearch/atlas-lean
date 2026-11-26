# Source Comparison Hom naturality

Naturality of `sourceComparisonHom` over `f : X ⟶ Y`.

States that
`substitutionSource (O ⋙ F).map f ≫ sourceComparisonHom Y`
equals
`sourceComparisonHom X ≫ F.map (substitutionSource O.map f)`.

Derived from `factorsIso_inv_naturality`, functoriality of
`FiniteTensor.tensor W`, `comparison_naturality`, and reassociation.
