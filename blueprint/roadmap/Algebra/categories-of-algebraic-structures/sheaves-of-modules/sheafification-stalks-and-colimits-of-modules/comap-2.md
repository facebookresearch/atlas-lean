# Preimage of a module-sheaf submodule

Let `C : Type u₁` have morphism universe `v₁`, `J` a Grothendieck topology, `R : Sheaf J
RingCat.{u}`, and `M,P : SheafOfModules.{v} R`. For a sheaf submodule `N≤P` and `f : M → P`,
`N.comap f` is the sheaf submodule of `M` whose component is the preimage `f_X⁻¹(N_X)` at each
object. Its underlying presheaf submodule is `N.toSubmodule.comap f.val`.
