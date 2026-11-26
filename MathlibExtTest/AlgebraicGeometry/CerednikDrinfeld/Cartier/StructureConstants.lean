/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.StructureConstants
public import MathlibExt.RingTheory.WittVector.CartierLift

@[expose] public noncomputable section

namespace CartierStructureConstantsTest

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

/-- Under `CartierLift.liftHom`, the lifts of structure constants to `CartierLift.LiftRing` map
back to them. -/
theorem exactSource (p : ℕ) [Fact p.Prime] {B : Type*} [CommRing B] (j : Zp2 p →+* B)
    (a : ℕ → Fin 2 → B) (h : a 0 0 * a 0 1 = p) :
    (fun m i => CartierLift.liftHom j (a 0 0) (a 0 1) h
      (CartierLift.liftConstants (p := p) (R := Zp2 p) a m i)) = a :=
  funext fun m => funext fun i => CartierLift.liftHom_liftConstants j a h m i

/-- The index of the `m`-th term of a structure-constant expansion alternates, starting from the
other piece. -/
example : GradedCartierModuleData.piIndex 0 0 = 1 ∧ GradedCartierModuleData.piIndex 0 1 = 0 ∧
    GradedCartierModuleData.piIndex 1 0 = 0 := by
  decide

/-- Structure constants to order one: `ϖ (γ 0)` is `homothety (a 0 0) (γ 1)` up to the image of
`V`, so the first term comes from the other piece. -/
example (p : ℕ) [Fact p.Prime] {B : Type*} [CommRing B] {X : FormalODModule p B}
    {γ : Fin 2 → CartierModule p X.F} {a : ℕ → Fin 2 → B} (h : X.HasStructureConstants γ a) :
    ∃ r : CartierModule p X.F,
      endAct X.varpiEnd (γ 0) = homothety (a 0 0) (γ 1) + verschiebungInt r := by
  obtain ⟨r, hr⟩ := h.exists_eq 0 1
  exact ⟨r, by simpa [GradedCartierModuleData.piIndex] using hr⟩

end CartierStructureConstantsTest
