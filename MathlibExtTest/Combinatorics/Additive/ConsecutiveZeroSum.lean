/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import MathlibExt.Combinatorics.Additive.ConsecutiveZeroSum

namespace MetaMathlibExt

/-- In the trivial group, the only term already forms a zero-sum block. -/
example (x : Fin 1 → ZMod 1) : ∃ a : ℤ, a = 1 ∧ a • x 0 = 0 := by
  have h := (consecutive_constant_eq_card (ZMod 1)).1.2
  rw [ZMod.card] at h
  obtain ⟨s, t, _, a, ha, hsum⟩ := h x
  rw [Fin.eq_zero s, Fin.eq_zero t] at ha hsum
  exact ⟨a 0, ha 0 (by simp), by simpa using hsum⟩

/-- In the Klein four-group, three terms can avoid every consecutive zero sum. -/
example : ∃ x : Fin 3 → ZMod 2 × ZMod 2, ∀ s t, s ≤ t → ∑ i ∈ Finset.Icc s t, x i ≠ 0 := by
  by_contra! hall
  have h : Fintype.card (ZMod 2 × ZMod 2) ≤ 3 := (consecutive_constant_eq_card _).2 (by
    refine ⟨by decide, fun x => ?_⟩
    obtain ⟨s, t, hst, hsum⟩ := hall x
    exact ⟨s, t, hst, fun _ => 1, fun _ _ => rfl, by simpa using hsum⟩)
  simp [Fintype.card_prod, ZMod.card] at h

end MetaMathlibExt
