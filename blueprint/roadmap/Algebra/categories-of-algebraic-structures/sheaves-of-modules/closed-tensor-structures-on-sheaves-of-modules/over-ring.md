# Presheaf of rings on the slice site

Let `C : Type u` have morphism universe `u`, `J` be a topology, `R : Sheaf J CommRingCat.{u}`,
and `X∈C`. The presheaf `overRing R X : (Over X)ᵒᵖ ⥤ RingCat.{u}` is the underlying ring
presheaf of `R.over X`. At an object `Y→X`, its ring is the underlying ring of `R(Y)`.
