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

-- Precision zero is a formal extension, not a floating-point format.
#guard rsum 0 ([1] : List ℚ) = 0
#guard rsum 0 ([3 / 2] : List ℚ) = 2

example : ¬Cslib.Algorithms.Lean.FloatingPoint.IsFloat 0 (2 : ℚ) := by
  rintro ⟨m, e, hm, hx⟩
  have hm0 : m = 0 := by
    rw [pow_zero, abs_lt] at hm
    omega
  simp [hm0] at hx

example (p : ℕ) (hp : 1 ≤ p) (xs : List ℚ) :
    Cslib.Algorithms.Lean.FloatingPoint.IsFloat p (rsum p xs) := by
  cases xs with
  | nil => exact ⟨0, 0, by positivity, by simp [rsum]⟩
  | cons x xs => exact Cslib.Algorithms.Lean.FloatingPoint.isFloat_fl hp _

example (p : ℕ) : rsum p ([] : List ℝ) = 0 := rfl

example (p : ℕ) : rsum p ([0, 0] : List ℝ) = 0 := by
  simp [rsum, Cslib.Algorithms.Lean.FloatingPoint.fl_zero]

example : |rsum 0 ([1, -1, 3] : List ℝ) - 3| ≤ 35 := by
  have h := rsum_abs_sub_le 0 ([1, -1, 3] : List ℝ)
  norm_num [unitRoundoff] at h ⊢
  exact h

#print axioms CSLibExt.Algorithms.Lean.Numerical.Summation.rsum_bound
#print axioms CSLibExt.Algorithms.Lean.Numerical.Summation.rsum_abs_sub_le
