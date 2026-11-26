# Fixed local rank from free sheaves on a covering family

Let `C : Type u₁` have morphism universe `v₁`, `J` a Grothendieck topology, and `R : Sheaf J
RingCat.{u}`. Assume `HasSheafify` for additive presheaves and `WEqualsLocallyBijective` on
every `J.over X`. For `M : SheafOfModules.{u} R`, `n : ℕ`, a cover `X : I → C` with `I : Type
u₁`, sets `Ix i : Type u`, and isomorphisms `free_{R.over(X i)}(Ix i) ≅ M.over (X i)`, if
every `Ix i` admits an equivalence with `Fin n`, then `IsLocallyFreeOfRank M n`.
