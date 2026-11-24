# Precomp Comp

For functors `K : B ⥤ A` and `L : B₂ ⥤ B`, the composite
`precompFunctor K ⋙ precompFunctor L` is naturally isomorphic to `precompFunctor (L ⋙ K)`
as functors from `LeftModule A T` to `LeftModule B₂ T`. Its component at `M` is
`(M.precomp K).precomp L ≅ M.precomp (L ⋙ K)`.
