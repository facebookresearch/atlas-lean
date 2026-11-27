# Restrict Scalars Equivalence Of Ring Equiv

Restriction of scalars along a ring equivalence, restricted to finitely
generated projective modules.

For `e : R ≃+* S`, the forward functor has orientation
`FGProjectiveCat S ⥤ FGProjectiveCat R`, exactly matching
`ModuleCat.restrictScalars e.toRingHom`.  Ring universes are independent and
the module-carrier universe `v` is shared by source and target.
