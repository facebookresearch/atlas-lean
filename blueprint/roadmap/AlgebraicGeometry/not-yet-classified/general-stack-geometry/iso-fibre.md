# Iso Fibre

The 2-fibre product of categories of functors `f : A ⥤ C` and `g : B ⥤ C`, the categorical
pullback: its objects are triples `(a, b, f a ≅ g b)` and its morphisms are pairs of morphisms
commuting with the comparison isomorphisms. Its projections are `Limits.CategoricalPullback.π₁` and
`π₂`, its 2-cell is the `CatCommSq` instance, and functors from a category `X` into it correspond
to pairs of functors `X ⥤ A`, `X ⥤ B` with a natural isomorphism between their composites with `f`
and `g` (`Limits.CategoricalPullback.functorEquiv`).
