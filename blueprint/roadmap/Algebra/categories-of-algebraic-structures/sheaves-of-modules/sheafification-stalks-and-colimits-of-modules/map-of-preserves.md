# Map Of Preserves

Transport a presentation along a colimit-preserving functor: the image of
the generator epi, with relations transported through the free comparison
isos. Needs only shape-colimit preservation for the two discrete index types
plus preservation of the single relation colimit. This cannot use Mathlib's
`Presentation.map`, which needs `PreservesColimitsOfSize.{u, u}` (whose
derivation needs `HasPullbacks`, absent at the call site).
