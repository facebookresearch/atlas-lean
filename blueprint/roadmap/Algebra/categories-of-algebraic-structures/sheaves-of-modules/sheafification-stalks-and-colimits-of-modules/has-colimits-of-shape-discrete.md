# Small indexed coproducts of module sheaves

Let `D : Type u₁` have morphism universe `v₁`, `L` be a Grothendieck topology, and `S : Sheaf
L RingCat.{u}`. Assume `HasWeakSheafify L AddCommGrpCat.{u}` and `L.WEqualsLocallyBijective
AddCommGrpCat.{u}`. For `I : Type wI` with `Small.{u} I`, `SheafOfModules.{u} S` has colimits
of shape `Discrete I`. Thus all coproducts with an index set of size at most `u` exist.
