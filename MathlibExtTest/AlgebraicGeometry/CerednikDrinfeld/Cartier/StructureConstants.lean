/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.StructureConstants

@[expose] public noncomputable section

namespace CartierStructureConstantsTest

open CerednikDrinfeld

/-- Under `CartierLift.liftHom`, the lifts of structure constants to `CartierLift.LiftRing` map
back to them. -/
theorem exactSource (p : ℕ) [Fact p.Prime] {B : Type*} [CommRing B] (j : Zp2 p →+* B)
    (a : ℕ → Fin 2 → B) (h : a 0 0 * a 0 1 = p) :
    (fun m i => CartierLift.liftHom j (a 0 0) (a 0 1) h
      (CartierLift.liftConstants (p := p) (R := Zp2 p) a m i)) = a :=
  FormalODModule.liftHom_comp_liftConstants j a h

/-- The index of the `m`-th term of a structure-constant expansion alternates, starting from the
other piece. -/
example : FormalODModule.piIndex 0 0 = 1 ∧ FormalODModule.piIndex 0 1 = 0 ∧
    FormalODModule.piIndex 1 0 = 0 := by
  decide

end CartierStructureConstantsTest
