/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.WhittGeneralizedCatalan
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : whittGeneralizedCatalan 5 0 = 0 := whittGeneralizedCatalan_zero 5

example : whittGeneralizedCatalan (-3) 1 = 1 := whittGeneralizedCatalan_one (-3)

example : whittGeneralizedCatalan 0 7 = 1 := whittGeneralizedCatalan_zero_left (by decide)

example : whittGeneralizedCatalan 2 4 = 67 := whittGeneralizedCatalan_two_small.2.2.2

/-- `α = 1` gives the Catalan numbers `1, 2, 5`. -/
example : whittGeneralizedCatalan 1 1 = 1 ∧ whittGeneralizedCatalan 1 2 = 2 ∧
    whittGeneralizedCatalan 1 3 = 5 := by
  simp [whittGeneralizedCatalan, Finset.sum_range_succ, Nat.choose]
  norm_num

/-- `C(3, 3) = 25`. -/
example : whittGeneralizedCatalan 3 3 = 25 := by
  simp [whittGeneralizedCatalan, Finset.sum_range_succ, Nat.choose]
  norm_num

example (n : ℕ) : whittGeneralizedCatalan 2 (n + 1) =
    ∑ k ∈ Finset.range (n + 1), (1 - (k : ℚ) / ((n : ℚ) + 1)) * ((n + k).choose k : ℚ) * 2 ^ k :=
  whittGeneralizedCatalan_succ 2 n

end MetaMathlibExt
