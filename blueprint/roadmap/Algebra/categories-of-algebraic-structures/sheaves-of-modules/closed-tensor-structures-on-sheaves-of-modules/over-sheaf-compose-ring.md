# Underlying ring sheaf after restriction to a slice

Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and `X∈C`. Assuming the
underlying-ring sheaf comparison on `J.over X`, `overSheafComposeRing R X` is the underlying
ring sheaf of `R.over X`, namely `(sheafCompose (J.over X) (forget₂ CommRingCat RingCat)).obj
(Sheaf.over R X)`.
