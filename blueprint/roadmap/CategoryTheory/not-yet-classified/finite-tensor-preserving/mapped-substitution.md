# Mapped Substitution

Mapped substitution as an `ColoredOperadSubstitution (O.toCollection ⋙ F)`,
with `app X = sourceComparisonHom p O.toCollection X ≫ F.map (O.subst.app X)`.

Naturality follows from `sourceComparisonHom_naturality`,
`F.map_comp`, `O.subst.naturality`, and the definitional form of
`substitutionTarget` for a postcomposed collection.
