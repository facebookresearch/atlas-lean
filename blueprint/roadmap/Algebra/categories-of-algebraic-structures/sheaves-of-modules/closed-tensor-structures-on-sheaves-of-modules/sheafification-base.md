# Module sheafification on the base site

Let `(C,J)` be a site at universe `u` and `R : Sheaf J CommRingCat.{u}`. Assume weak additive
sheafification, `J.WEqualsLocallyBijective Ab.{u}`, and the underlying-ring sheaf comparison.
The functor `sheafificationBase R` is `PresheafOfModules.sheafificationCommId R`, from module
presheaves over `R.obj ⋙ forget₂ CommRingCat RingCat` to module sheaves over `sheafComposeRing
R`.
