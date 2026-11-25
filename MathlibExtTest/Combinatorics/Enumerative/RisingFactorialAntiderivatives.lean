/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RisingFactorialAntiderivatives
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

/-! # Tests for rising-factorial weighted sums -/

open MetaMathlibExt

-- At order zero and at the origin, only the constant coefficient survives.
example (a : ℕ → ℝ) (I : ℕ → ℝ → ℝ)
    (hI0 : ∀ y, I 0 y = ∑ k ∈ Finset.range (1 + 1), a k * y ^ k)
    (hI : ∀ j y, HasDerivAt (I (j + 1)) (I j y) y) : a 0 = I 0 0 := by
  simpa [Finset.sum_range_succ] using
    sum_coeff_mul_pow_div_ascFactorial_eq_antideriv a 1 0 I hI0 hI 0

-- The shifted divided powers start at 1 and have generally nonzero constants.
-- Two integrations give a correction with both a linear and a constant term.
example (b x : ℝ) :
    x ^ 2 / 2 = (x + b) ^ 2 / 2 - (b * x + b ^ 2 / 2) := by
  let I (j : ℕ) (y : ℝ) := (y + b) ^ j / j.factorial
  have hI (j : ℕ) (y : ℝ) : HasDerivAt (I (j + 1)) (I j y) y := by
    have hy : HasDerivAt (fun z : ℝ ↦ z + b) 1 y := (hasDerivAt_id' y).add_const b
    have h := (hy.pow (j + 1)).div_const ((j + 1).factorial : ℝ)
    have hj : (↑(j + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.succ_ne_zero
    simpa only [I, Pi.pow_apply, Nat.add_one_sub_one, mul_one, Nat.factorial_succ, Nat.cast_mul,
      mul_div_mul_left _ _ hj] using h
  have h := sum_coeff_mul_pow_div_ascFactorial_eq_antideriv (fun _ ↦ 1) 0 2 I
    (by simp [I]) hI x
  rw [show Finset.Icc 1 2 = {1, 2} from by decide] at h
  norm_num [I, Nat.factorial, Nat.ascFactorial] at h
  exact h

-- The degree-zero binomial still contributes the single shifted monomial.
example :
    (∑ k ∈ Finset.range (0 + 1), ((0 : ℕ).choose k : ℝ) * 3 ^ (k + 2) /
      (k + 1).ascFactorial 2) = 9 / 2 := by
  rw [sum_choose_mul_pow_div_ascFactorial 0 2 (by decide)]
  rw [show Finset.Icc 1 (2 - 1) = {1} from by decide]
  norm_num [Nat.ascFactorial, Nat.factorial]

-- At x = -1 the full binomial expansion vanishes, but the tail does not.
example :
    (∑ k ∈ Finset.range (2 + 1), ((2 : ℕ).choose k : ℝ) * (-1) ^ (k + 2) /
      (k + 1).ascFactorial 2) = 1 / 4 := by
  rw [sum_choose_mul_pow_div_ascFactorial 2 2 (by decide)]
  rw [show Finset.Icc 1 (2 - 1) = {1} from by decide]
  norm_num [Nat.ascFactorial, Nat.factorial]

-- At order one there are no positive low-degree terms to subtract.
example (N : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * x ^ (k + 1) /
      (k + 1).ascFactorial 1) = ((1 + x) ^ (N + 1) - 1) / (N + 1).ascFactorial 1 := by
  rw [sum_choose_mul_pow_div_ascFactorial N 1 (by decide)]
  simp
