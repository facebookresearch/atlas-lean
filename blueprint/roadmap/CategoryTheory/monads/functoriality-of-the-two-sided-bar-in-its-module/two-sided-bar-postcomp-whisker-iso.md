# Two Sided Bar Postcomp Whisker Iso

Target-postcomposition comparison with whiskered source.

The source is literally the whiskered bar `twoSidedBar T R L ⋙ functorPostcompOuter K`, not
`toSimplicialFunctor.obj (Data.mapObj _ _)`. It composes the generic
`toSimplicialFunctor_mapFunctorIso` bridge with the transport of the data-level
`barDataPostcompOuterIso` (functor associator orientation preserved).
