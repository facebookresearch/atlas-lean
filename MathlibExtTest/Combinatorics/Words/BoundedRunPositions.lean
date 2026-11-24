/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.BoundedRunPositions

/-! # Tests for position bounds in words with bounded runs -/

namespace MetaMathlibExt.letterPosition_le_of_run_le

-- The first a is at zero, and the signed position of the first b is between one and c.
example {w : ℕ → Bool} (hw : BothLettersInfinite w) (h₀ : w 0 = true) {c : ℕ}
    (hc : ∀ i k, (∀ j < k, w (i + j) = w i) → k ≤ c) :
    letterPosition w true 1 = 0 ∧ 1 ≤ relativePosition w 1 ∧ relativePosition w 1 ≤ c := by
  obtain ⟨ha, _, hr⟩ := letterPosition_le_of_run_le hw h₀ hc 1 le_rfl
  simpa using And.intro ha hr

private def abb (i : ℕ) : Bool := decide (i % 3 = 0)

-- At the fourth occurrences in abbabb…, the corrected lower bound is -5 and the
-- printed lower bound is -3. The actual difference is -4.
example : -5 ≤ relativePosition abb 4 ∧ relativePosition abb 4 = -4 := by
  have inf : BothLettersInfinite abb := by
    constructor <;> apply Set.infinite_of_forall_exists_gt <;> intro n
    · exact ⟨3 * (n + 1), by simp [abb], by omega⟩
    · exact ⟨3 * (n + 1) + 1, by simp [abb], by omega⟩
  have run (i k : ℕ) (h : ∀ j < k, abb (i + j) = abb i) : k ≤ 2 := by
    by_contra! hk
    have h₁ := h 1 (by omega)
    have h₂ := h 2 (by omega)
    simp only [abb, decide_eq_decide] at h₁ h₂
    omega
  have bound := (letterPosition_le_of_run_le inf rfl run 4 (by decide)).2.2.1
  have ha := Nat.nth_count (p := fun i => abb i = true) (n := 9) (by decide)
  have hb := Nat.nth_count (p := fun i => abb i = false) (n := 5) (by decide)
  change letterPosition abb true 4 = 9 at ha
  change letterPosition abb false 4 = 5 at hb
  exact ⟨bound, by simp [relativePosition, ha, hb]⟩

end MetaMathlibExt.letterPosition_le_of_run_le
