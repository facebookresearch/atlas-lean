# Restriction of module sheaves to a slice

Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`, with
underlying-ring sheaf comparisons on the base and slice sites. The functor `restrictSheaf R X`
sends module sheaves over `sheafComposeRing R` to those over `overSheafComposeRing R X`. It is
`SheafOfModules.overFunctor (sheafComposeRing R) X`, with the canonical identification of the
target ring sheaves.
