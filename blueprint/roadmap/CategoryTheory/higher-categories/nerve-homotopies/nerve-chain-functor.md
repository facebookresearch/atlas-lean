# Nerve Chain Functor

The functor `C × Fin 3 ⥤ D` classified by a chain of natural
transformations `α : F ⟶ G` and `β : G ⟶ H`: the composite of
`Prod.swap` with the uncurrying of `ComposableArrows.mk₂ α β`. Its
prism is a `2`-simplex of the functor object `Fun(nerve C, nerve D)`
through `SSet.ihomSimplexOfPrism`.
