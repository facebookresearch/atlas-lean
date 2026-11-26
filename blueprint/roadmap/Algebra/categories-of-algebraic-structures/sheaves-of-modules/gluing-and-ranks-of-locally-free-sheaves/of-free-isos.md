# Local freeness from free sheaves on a covering family

Let `C : Type u₁` have morphism universe `v₁`, `J` a Grothendieck topology, and `R : Sheaf J
RingCat.{u}`. Assume weak additive sheafification and `WEqualsLocallyBijective` on every
`J.over X`. For `M : SheafOfModules.{u} R`, a covering family `X : I → C` with `I : Type w`,
sets `Ix i : Type u`, and isomorphisms `free_{R.over(X i)}(Ix i) ≅ M.over (X i)`, the sheaf
`M` is locally free.
