# Preimage of a module-presheaf submodule

Let `C : Type u₁` have morphism universe `v₁`, `R : Cᵒᵖ ⥤ RingCat.{u}`, and `M,P` be module
presheaves of carrier universe `v`. For a submodule presheaf `N≤P` and a morphism `f : M → P`,
`N.comap f` is the submodule presheaf of `M` with component `Submodule.comap (f.app X).hom
(N.obj X)` at `X : Cᵒᵖ`. Equivalently, its sections are those whose images under `f` lie in
`N`.
