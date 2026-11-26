# Underlying module presheaf on the slice site

Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`, with the
underlying-ring sheaf comparison on `J.over X`. The functor `forgetRestrictOver R X` sends
module sheaves over `overSheafComposeRing R X` to module presheaves over `overRing R X`, by
forgetting and restricting scalars along `Sheaf.commRingCatForget₂Id (Sheaf.over R X)`.
