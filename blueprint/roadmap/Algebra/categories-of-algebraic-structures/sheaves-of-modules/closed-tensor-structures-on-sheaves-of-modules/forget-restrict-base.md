# Underlying module presheaf with the commutative-ring indexing

Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and assume the
underlying-ring sheaf comparison. Write `R_s=sheafComposeRing R` and `R_p=R.obj ⋙ forget₂
CommRingCat RingCat`. The functor `forgetRestrictBase R : SheafOfModules R_s →
PresheafOfModules R_p` forgets the sheaf structure and reindexes the ring action along
`Sheaf.commRingCatForget₂Id R`.
