# Two Sided Bar Precomp Whisker Iso

Genuine source-precomposition comparison with whiskered source.

The source is literally the whiskered genuine bar
`twoSidedBar T R L ⋙ functorPrecompOuter H`, not
`toSimplicialFunctor.obj (Data.mapObj _ _)`. It composes the generic
`toSimplicialFunctor_mapFunctorIso` bridge with the existing genuine
transport of the data-level `barDataPrecompOuterIso` (double-associator
orientation preserved). No simplicial identity is reproved.
