# Map DGHomotopy Category

The functor `H⁰(F) : H⁰(C) ⥤ H⁰(D)` induced by a DG functor `F`.  On morphisms it is the map
induced by `F.map X Y` on degree-zero cohomology of Hom complexes; by
`CategoryTheory.EnrichedFunctor.mapDGHomotopyCategory_map_homOf` it sends the class of a closed
morphism `f` to the class of `F f`.
