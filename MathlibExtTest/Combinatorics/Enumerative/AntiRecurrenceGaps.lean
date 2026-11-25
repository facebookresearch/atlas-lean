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
