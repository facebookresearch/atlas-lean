/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.AntitoneRelativePosition

/-! # Tests of non-increasing relative positions -/

namespace MetaMathlibExt.exists_word_relativePosition_eq_of_antitone

-- A constant gap of any positive size puts the first a exactly that far from the origin.
example (k : ℕ) : ∃ w, BothLettersInfinite w ∧ w 0 = false ∧
    letterPosition w true 1 = k + 1 ∧ ∀ n, 1 ≤ n → relativePosition w n = -((k : ℤ) + 1) := by
  obtain ⟨w, hw, hzero, hrel⟩ := exists_word_relativePosition_eq_of_antitone
    (fun _ => -((k : ℤ) + 1)) (by omega) (fun _ _ => le_rfl)
  have hfirst := hrel 1 le_rfl
  rw [relativePosition, letterPosition_one_of_head hzero] at hfirst
  exact ⟨w, hw, hzero, by omega, hrel⟩

-- The gap may grow without bound, even if the prescribed values increase from index zero to one.
example : ∃ w, BothLettersInfinite w ∧ w 0 = false ∧
    ∀ n, 1 ≤ n → relativePosition w n = -(n : ℤ) := by
  let r (n : ℕ) : ℤ := if n = 0 then -2 else -(n : ℤ)
  have hanti (n : ℕ) (hn : 1 ≤ n) : r (n + 1) ≤ r n := by
    simp [r, Nat.ne_zero_of_lt hn]
  obtain ⟨w, hw, hzero, hrel⟩ := exists_word_relativePosition_eq_of_antitone r (by decide) hanti
  exact ⟨w, hw, hzero, fun n hn => by simpa [r, Nat.ne_zero_of_lt hn] using hrel n hn⟩

end MetaMathlibExt.exists_word_relativePosition_eq_of_antitone
