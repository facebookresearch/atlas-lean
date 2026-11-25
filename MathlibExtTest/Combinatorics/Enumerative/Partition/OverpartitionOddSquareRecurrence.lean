/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.Partition.OverpartitionOddSquareRecurrence

namespace MetaMathlibExt.overpartitionOdd_square_recurrence

-- At zero, the square theta series counts the empty overpartition once.
example : overpartitionOddPartsCount 0 = 1 := by
  simpa using overpartitionOdd_square_recurrence 0

-- The first shift at the endpoint n = 2 contributes the empty overpartition.
private theorem count_two : overpartitionOddPartsCount 2 = 2 := by
  have h := overpartitionOdd_square_recurrence 2
  rw [show ((Finset.Icc 1 2).filter fun k : ℕ => 2 * k ^ 2 ≤ 2) = {1} by decide] at h
  norm_num [overpartitionOddPartsCount_zero, show
    2 ∉ (Finset.Icc 1 2).image (fun m : ℕ => m ^ 2) by decide] at h
  omega

-- The positive square n = 4 contributes both square roots.
example : overpartitionOddPartsCount 4 = 6 := by
  have h := overpartitionOdd_square_recurrence 4
  rw [show ((Finset.Icc 1 4).filter fun k : ℕ => 2 * k ^ 2 ≤ 4) = {1} by decide] at h
  norm_num [count_two, show 4 ∈ (Finset.Icc 1 4).image (fun m : ℕ => m ^ 2) by decide] at h
  omega

-- At n = 8 the second shift first appears, with positive sign.
example : overpartitionOddPartsCount 8 + 2 = 2 * overpartitionOddPartsCount 6 := by
  have h := overpartitionOdd_square_recurrence 8
  rw [show ((Finset.Icc 1 8).filter fun k : ℕ => 2 * k ^ 2 ≤ 8) = {1, 2} by decide] at h
  norm_num [Finset.sum_insert, overpartitionOddPartsCount_zero, show
    8 ∉ (Finset.Icc 1 8).image (fun m : ℕ => m ^ 2) by decide] at h
  omega

end MetaMathlibExt.overpartitionOdd_square_recurrence
