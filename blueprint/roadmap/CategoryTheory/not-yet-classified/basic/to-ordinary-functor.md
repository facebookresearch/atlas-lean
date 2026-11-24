# To Ordinary Functor

The honest underlying functor of an enriched functor between enriched
ordinary categories, as the standard Mathlib composite: back along the
domain's `ForgetEnrichment.equiv`, through `EnrichedFunctor.forget`, then
forward along the codomain's `ForgetEnrichment.equivFunctor`. Functoriality
is inherited from the composite, so no identity or composition proofs are
needed here. The weight and diagram of
`EnrichedWeightedBar.IndexingData` descend to ordinary functors this way, so
ordinary coends apply to enriched-built integrands.
