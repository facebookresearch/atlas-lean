# Iso Fibre

The 2-fibre product of categories: Mathlib's categorical pullback, whose objects are triples
`(a, b, f a ≅ g b)` and whose morphisms are pairs of morphisms commuting with the comparison
isomorphisms. Its projections are `Limits.CategoricalPullback.π₁` and `π₂`, its 2-cell is the
`CatCommSq` instance, and functors into it correspond to such data
(`Limits.CategoricalPullback.functorEquiv`).
