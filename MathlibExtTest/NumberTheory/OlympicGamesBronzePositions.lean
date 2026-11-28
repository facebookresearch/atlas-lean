/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OlympicGamesBronzePositions

/-!
# Tests for the bronze game

Check the first bronze and companion candidates, and compute legal moves at small heap sizes
from the public move rules, independently of the P-position theorem.
-/

namespace MetaMathlibExt

local notation "α" => ((3 + Real.sqrt 13) / 2)
local notation "β" => ((5 + Real.sqrt 13) / 6)

private theorem sqrt13_bounds : (18 : ℝ) / 5 < Real.sqrt 13 ∧ Real.sqrt 13 < 11 / 3 := by
  exact ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num),
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)⟩

private theorem alpha_values : beattySeq α 1 = 3 ∧ beattySeq α 2 = 6 ∧ beattySeq α 3 = 9 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [beattySeq, Int.floor_eq_iff] <;>
    constructor <;> linarith only [sqrt13_bounds.1, sqrt13_bounds.2]

private theorem beta_values : beattySeq β 1 = 1 ∧ beattySeq β 2 = 2 ∧ beattySeq β 3 = 4 ∧
    beattySeq β 4 = 5 ∧ beattySeq β 5 = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [beattySeq, Int.floor_eq_iff] <;>
    constructor <;> linarith only [sqrt13_bounds.1, sqrt13_bounds.2]

private theorem beatty_index_lt {t : ℝ} (ht : 0 ≤ t) {k l : ℤ}
    (h : beattySeq t k < beattySeq t l) : k < l := by
  apply lt_of_not_ge
  intro hkl
  exact h.not_ge (Int.floor_mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) ht))

private theorem alpha_small {n : ℤ} (hn : n ≤ 7) :
    (∃ k : ℤ, 0 < k ∧ beattySeq α k = n) ↔ n = 3 ∨ n = 6 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hlt : k < 3 := beatty_index_lt (t := α) (by positivity) (by rw [alpha_values.2.2]; omega)
    interval_cases k
    · exact Or.inl alpha_values.1
    · exact Or.inr alpha_values.2.1
  · rintro (rfl | rfl)
    · exact ⟨1, by decide, alpha_values.1⟩
    · exact ⟨2, by decide, alpha_values.2.1⟩

private theorem beta_small {n : ℤ} (hn : n ≤ 6) :
    (∃ k : ℤ, 0 < k ∧ beattySeq β k = n) ↔ n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 5 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hlt : k < 5 := beatty_index_lt (t := β) (by positivity)
      (by rw [beta_values.2.2.2.2]; omega)
    interval_cases k
    · exact Or.inl beta_values.1
    · exact Or.inr (Or.inl beta_values.2.1)
    · exact Or.inr (Or.inr (Or.inl beta_values.2.2.1))
    · exact Or.inr (Or.inr (Or.inr beta_values.2.2.2.1))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, by decide, beta_values.1⟩
    · exact ⟨2, by decide, beta_values.2.1⟩
    · exact ⟨3, by decide, beta_values.2.2.1⟩
    · exact ⟨4, by decide, beta_values.2.2.2.1⟩

example : lucasU bronzeLucasParams 1 = 1 ∧ bronzeCompanionFirst 2 = 4 ∧
    bronzeCompanionSecond 2 = 7 ∧ lucasU bronzeLucasParams 3 = 10 := by decide

-- The empty heap and the first positive candidate are both terminal.
example (m : ℕ) : ¬beattyOctalMove α β 0 m := fun h => Nat.not_lt_zero m (beattyOctalMove_lt h)

example (m : ℕ) : ¬beattyOctalMove α β 1 m := by
  intro h
  obtain rfl : m = 0 := by have := beattyOctalMove_lt h; omega
  have hα := (beattyOctalMove_zero_iff.mp h).2
  rw [alpha_small (by norm_num)] at hα
  omega

-- A positive index of the zero-slope sequence gives 0, but an empty heap cannot be removed.
example : beattySeq 0 1 = 0 ∧ ¬beattyOctalMove 0 2 0 0 := by
  constructor
  · simp [beattySeq]
  · rw [beattyOctalMove_zero_iff]
    simp

-- The second sequence may likewise contain 0, but a partial move must remove a token.
example : beattySeq 0 1 = 0 ∧ ¬beattyOctalMove 2 0 1 1 := by
  constructor
  · simp [beattySeq]
  · rw [beattyOctalMove_pos_iff (by decide : 0 < (1 : ℕ))]
    simp

-- Check absorption through both types of move.
example : beattyOctalMove α β 3 0 :=
  beattyOctalMove_zero_iff.mpr ⟨by decide, 1, by decide, alpha_values.1⟩

example : beattyOctalMove α β 2 1 :=
  (beattyOctalMove_pos_iff (by decide)).mpr ⟨by decide, 1, by decide, beta_values.1⟩

-- The first companion has no move to 0 or 1, but does have both legal partial removals.
example (m : ℕ) : beattyOctalMove α β 4 m ↔ m = 2 ∨ m = 3 := by
  by_cases hm : m = 0
  · subst m
    rw [beattyOctalMove_zero_iff, alpha_small (by norm_num)]
    norm_num
  · rw [beattyOctalMove_pos_iff (Nat.pos_of_ne_zero hm)]
    constructor
    · rintro ⟨hlt, h⟩
      rw [beta_small (by omega)] at h
      omega
    · rintro (rfl | rfl)
      · exact ⟨by decide, 2, by decide, beta_values.2.1⟩
      · exact ⟨by decide, 1, by decide, beta_values.1⟩

-- The second companion has four followers, none of which is a smaller candidate.
example (m : ℕ) : beattyOctalMove α β 7 m ↔ m = 2 ∨ m = 3 ∨ m = 5 ∨ m = 6 := by
  by_cases hm : m = 0
  · subst m
    rw [beattyOctalMove_zero_iff, alpha_small (by norm_num)]
    norm_num
  · rw [beattyOctalMove_pos_iff (Nat.pos_of_ne_zero hm)]
    constructor
    · rintro ⟨hlt, h⟩
      rw [beta_small (by omega)] at h
      omega
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨by decide, 4, by decide, beta_values.2.2.2.1⟩
      · exact ⟨by decide, 3, by decide, beta_values.2.2.1⟩
      · exact ⟨by decide, 2, by decide, beta_values.2.1⟩
      · exact ⟨by decide, 1, by decide, beta_values.1⟩

end MetaMathlibExt
