/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Modal.ProvabilityLogic.FrameCorrespondence

namespace Cslib.Modal

-- Decreasing natural numbers give an infinite frame on which every Löb instance is valid.
example (V : ℕ → Unit → Prop) (phi : Formula Unit) :
    (KripkeModel.mk inferInstance (· > ·) V).Valid (Formula.axiomLob phi) :=
  (frame_valid_axiomLob_iff (Atom := Unit) (W := ℕ) (· > ·)).2
    ⟨fun hab hbc ↦ Nat.lt_trans hbc hab, Nat.lt_wfRel.wf⟩ V phi

-- Reversing the relation preserves transitivity but admits the infinite chain 0, 1, 2, ...
example : ¬∀ (V : ℕ → Unit → Prop) (phi : Formula Unit),
    (KripkeModel.mk inferInstance (· < ·) V).Valid (Formula.axiomLob phi) := by
  intro h
  have hwf := ((frame_valid_axiomLob_iff (Atom := Unit) (· < ·)).1 h).2
  exact (wellFounded_iff_isEmpty_descending_chain.mp hwf).false ⟨id, Nat.lt_succ_self⟩

-- A single predecessor step terminates, but 2 sees 1 and 1 sees 0 while 2 does not see 0.
example : ¬∀ (V : ℕ → Unit → Prop) (phi : Formula Unit),
    (KripkeModel.mk inferInstance (fun a b ↦ a = b + 1) V).Valid (Formula.axiomLob phi) := by
  intro h
  obtain ⟨htrans, _⟩ := (frame_valid_axiomLob_iff (Atom := Unit) (fun a b : ℕ ↦ a = b + 1)).1 h
  exact (by decide : 2 ≠ 0 + 1) (htrans (a := 2) (b := 1) (c := 0) rfl rfl)

end Cslib.Modal
