# Forgetting module structure preserves sheaf colimits

Let `C : Type u₁` have morphism universe `v₁`, `J` a Grothendieck topology, `R : Sheaf J
RingCat.{u}`, and `K : Type w` a category with morphism universe `w'`. Assume weak additive
sheafification at carrier universe `v`, `J.WEqualsLocallyBijective AddCommGrpCat.{v}`, and
colimits of shape `K` in both `PresheafOfModules.{v} R.obj` and `AddCommGrpCat.{v}`. Then
`SheafOfModules.toSheaf.{v} R` preserves colimits of shape `K`.
