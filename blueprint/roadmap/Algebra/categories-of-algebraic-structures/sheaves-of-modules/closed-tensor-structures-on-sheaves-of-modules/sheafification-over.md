# Module sheafification on a slice site

Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`. Assume weak
additive sheafification, the locally-bijective comparison, and the underlying-ring sheaf
comparison on `J.over X`. The functor `sheafificationOver R X` is `sheafificationCommId
(Sheaf.over R X)`, from module presheaves over `overRing R X` to module sheaves over
`overSheafComposeRing R X`.
