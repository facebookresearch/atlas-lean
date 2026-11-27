/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AntiRecurrenceGaps

open MetaMathlibExt

example {n : ℕ} (hn : 1 ≤ n) : antiRecurrence [1, 2] n + 6 ≤ antiRecurrence [1, 2] (n + 1) :=
  (antiRecurrence_add_length_mul_sum_le [1, 2] (by simp) (by decide) hn).1

-- The first two blocks for [1, 2] are [1, 2] and [3, 4].
example : antiRecurrence [1, 2] 2 = antiRecurrence [1, 2] 1 + 6 := by
  apply (antiRecurrence_add_length_mul_sum_le [1, 2] (by simp) (by decide) (n := 1)
    (by decide)).2.1
  decide +kernel

-- For [2, 1], the block [3, 5] lies between the intervals [1, 2] and [6, 7].
example : antiRecurrence [2, 1] 1 + 6 < antiRecurrence [2, 1] 2 := by
  apply (antiRecurrence_add_length_mul_sum_le [2, 1] (by simp) (by decide) (n := 1)
    (by decide)).2.2
  decide +kernel

example : antiRecurrence [2, 1] 2 + 6 < antiRecurrence [2, 1] 3 := by
  apply (antiRecurrence_add_length_mul_sum_le [2, 1] (by simp) (by decide) (n := 2)
    (by decide)).2.2
  decide +kernel

-- At I₃ the first two complement entries of the bounded form [1, 2] are 15 and 16.
example : antiRecurrence [1, 2] 3 ∈ Finset.Icc 15 21 ∧
    antiRecurrenceComplement [1, 2] 13 = 15 ∧ antiRecurrenceComplement [1, 2] 14 = 16 := by
  have h := antiRecurrence_mem_Icc_of_bounded [1, 2] (by simp) (by decide)
    (by decide +kernel) (n := 3) (by decide)
  exact ⟨h.1, h.2 0 (by decide), h.2 1 (by decide)⟩

-- For [1, 1], the fourth hole has offset 3, immediately after the first block of I₄.
example : antiRecurrence [1, 1] 4 = 18 ∧
    antiRecurrenceComplement [1, 1] 13 = 16 ∧ antiRecurrenceComplement [1, 1] 14 = 17 := by
  decide +kernel
