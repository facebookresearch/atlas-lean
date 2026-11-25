# Two Sided Bar Precomp Whisker Iso

Source-precomposition comparison with whiskered source.

The source is literally the whiskered bar `twoSidedBar T R L ⋙ functorPrecompOuter H`, not
`toSimplicialFunctor.obj (Data.mapObj _ _)`. It composes the generic
`toSimplicialFunctor_mapFunctorIso` bridge with the transport of the data-level
`barDataPrecompOuterIso` (double-associator orientation preserved).
