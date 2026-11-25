# Classifying Nerve Data Iso

Data-level classifying nerve isomorphism.

Assembled from the degreewise `tupleIso` with `Data.isoOfIso`; no `Iso.refl`
across ambient categories and no whiskered-functor iso is used.
`ClassifyingNerveSimplicial.lean` promotes this with `toSimplicialFunctor` as
`barNerveSimplicialIso` and composes with evaluated `classifyingBar` as
`classifyingNerveSimplicialIso`.
