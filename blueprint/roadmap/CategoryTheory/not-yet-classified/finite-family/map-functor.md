# Map Functor

Functoriality of `FiniteFamily.map` in the functor argument.

`mapFunctor` sends `F : C₁ ⥤ D` to `FiniteFamily.map F` and `α : F ⟶ G` to
`mapNatTrans α`. This reuses `map` and `mapNatTrans` without duplicating data.
