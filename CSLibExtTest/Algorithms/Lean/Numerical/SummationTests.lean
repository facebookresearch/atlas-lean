/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Numerical.Summation
public meta import CSLibExt.Algorithms.Lean.Numerical.Summation

/-! # Rounded-summation regression witnesses -/

open CSLibExt.Algorithms.Lean.Numerical.Summation

#guard rsum 2 ([] : List ℚ) = 0
#guard rsum 2 ([0, 0, 0] : List ℚ) = 0
#guard rsum 2 ([1] : List ℚ) = 1
#guard rsum 2 ([5] : List ℚ) = 4
#guard rsum 2 ([7] : List ℚ) = 8
#guard rsum 2 ([-5] : List ℚ) = -4
#guard rsum 2 ([-7] : List ℚ) = -8
#guard rsum 2 ([16, 1, -16] : List ℚ) = 0
#guard rsum 2 ([16, -16, 1] : List ℚ) = 0
#guard rsum 2 ([1, 16, -16] : List ℚ) = 1

example (p : ℕ) : rsum p ([] : List ℝ) = 0 := rfl

example (p : ℕ) : rsum p ([0, 0] : List ℝ) = 0 := by
  simp [rsum, Cslib.Algorithms.Lean.FloatingPoint.fl_zero]

example : |rsum 0 ([1, -1, 3] : List ℝ) - 3| ≤ 35 := by
  have h := rsum_abs_sub_le 0 ([1, -1, 3] : List ℝ)
  norm_num [unitRoundoff] at h ⊢
  exact h

#print axioms CSLibExt.Algorithms.Lean.Numerical.Summation.rsum_bound
#print axioms CSLibExt.Algorithms.Lean.Numerical.Summation.rsum_abs_sub_le
