/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.MonotoneRelativePosition

/-! # Tests of non-decreasing relative positions -/

namespace MetaMathlibExt.exists_word_relativePosition_eq_of_monotone

-- A constant positive gap determines the position of the first b.
example (k : ℕ) : ∃ w, BothLettersInfinite w ∧ w 0 = true ∧
    letterPosition w false 1 = k + 1 ∧ ∀ n, 1 ≤ n → relativePosition w n = (k : ℤ) + 1 := by
  obtain ⟨w, hw, hzero, hrel⟩ := exists_word_relativePosition_eq_of_monotone
    (fun _ => k + 1) (fun _ _ => Nat.succ_le_succ (Nat.zero_le k)) (fun _ _ => le_rfl)
  have hfirst := hrel 1 le_rfl
  rw [relativePosition, letterPosition_one_of_head hzero] at hfirst
  exact ⟨w, hw, hzero, by omega, fun n hn => by simpa using hrel n hn⟩

-- The prescribed sequence may grow without bound and may drop from index zero to index one.
example : ∃ w, BothLettersInfinite w ∧ w 0 = true ∧
    ∀ n, 1 ≤ n → relativePosition w n = (n : ℤ) := by
  let r (n : ℕ) : ℕ := if n = 0 then 2 else n
  have hpos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ r n := by
    simp [r, Nat.ne_zero_of_lt hn, hn]
  have hmono (n : ℕ) (hn : 1 ≤ n) : r n ≤ r (n + 1) := by
    simp [r, Nat.ne_zero_of_lt hn]
  obtain ⟨w, hw, hzero, hrel⟩ := exists_word_relativePosition_eq_of_monotone r hpos hmono
  exact ⟨w, hw, hzero, fun n hn => by simpa [r, Nat.ne_zero_of_lt hn] using hrel n hn⟩

end MetaMathlibExt.exists_word_relativePosition_eq_of_monotone
