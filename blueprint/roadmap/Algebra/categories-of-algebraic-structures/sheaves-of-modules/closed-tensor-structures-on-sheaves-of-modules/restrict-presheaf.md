# Restriction of module presheaves to a slice

Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`. The functor
`restrictPresheaf R X` sends module presheaves over the underlying ring presheaf of `R` to
module presheaves over `overRing R X`. It precomposes the presheaf with `(Over.forget X).op`,
retaining the corresponding ring actions and restriction maps.
