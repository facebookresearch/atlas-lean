/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ShiftedLucasQNegOneComposite

open MetaMathlibExt

-- At P = 1 and n = 0 the same positive K gives three consecutive composite integers.
example : ∃ K : ℤ, 0 < K ∧
    (1 < K - 1 ∧ ¬ (K - 1).natAbs.Prime) ∧
    (1 < K ∧ ¬ K.natAbs.Prime) ∧ (1 < K + 1 ∧ ¬ (K + 1).natAbs.Prime) := by
  obtain ⟨K, hK, h⟩ := exists_shift_lucasU_q_neg_one_composite (P := 1) (by decide)
  refine ⟨K, hK, ?_, ?_, ?_⟩
  · simpa [lucasU, sub_eq_add_neg] using h 0 (-1) (by simp)
  · simpa [lucasU] using h 0 0 (by simp)
  · simpa [lucasU] using h 0 1 (by simp)

-- The special parameter P = 22 has a single shift that works on both sides of a cycle boundary.
example : ∃ K : ℤ, 0 < K ∧
    (1 < lucasU ⟨22, -1, by decide⟩ 23 + K - 1 ∧
      ¬ (lucasU ⟨22, -1, by decide⟩ 23 + K - 1).natAbs.Prime) ∧
    (1 < lucasU ⟨22, -1, by decide⟩ 24 + K + 1 ∧
      ¬ (lucasU ⟨22, -1, by decide⟩ 24 + K + 1).natAbs.Prime) := by
  obtain ⟨K, hK, h⟩ := exists_shift_lucasU_q_neg_one_composite (P := 22) (by decide)
  exact ⟨K, hK, by simpa only [sub_eq_add_neg] using h 23 (-1) (by simp), h 24 1 (by simp)⟩

-- A parameter in the 2 mod 6 case, at the first term involving P in the recurrence.
example : ∃ K : ℤ, 0 < K ∧ 1 < 8 + K ∧ ¬ (8 + K).natAbs.Prime := by
  obtain ⟨K, hK, h⟩ := exists_shift_lucasU_q_neg_one_composite (P := 8) (by decide)
  have h₂ : lucasU ⟨8, -1, by decide⟩ 2 = 8 := rfl
  exact ⟨K, hK, by simpa only [h₂, add_zero] using h 2 0 (by simp)⟩
