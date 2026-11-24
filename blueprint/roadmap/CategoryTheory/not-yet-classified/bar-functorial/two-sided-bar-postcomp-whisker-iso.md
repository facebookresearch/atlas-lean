# Two Sided Bar Postcomp Whisker Iso

Genuine target-postcomposition comparison with whiskered source.

The source is literally the whiskered genuine bar
`twoSidedBar T R L ⋙ functorPostcompOuter K`, not
`toSimplicialFunctor.obj (Data.mapObj _ _)`. It composes the generic
`toSimplicialFunctor_mapFunctorIso` bridge with the existing genuine
transport of the data-level `barDataPostcompOuterIso` (functor associator
orientation preserved). No simplicial identity is reproved.
