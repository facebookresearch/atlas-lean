/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FibonacciPiSquared
import Mathlib.Tactic.Ring

namespace MetaMathlibExt.fibPiSquared_coeff_eq_fib

private noncomputable def coeff : ℕ → ℝ
  | 0 => -(8 * √5) / 250
  | 1 => (25 - 4 * √5) / 250
  | n + 2 => coeff (n + 1) + coeff n

private theorem coeff_step (n : ℕ) (hn : 1 ≤ n) : coeff (n + 1) = coeff n + coeff (n - 1) := by
  cases n with
  | zero => omega
  | succ n => rw [coeff, Nat.succ_sub_one]

example : coeff 1 = (25 - 4 * √5) / 250 := by
  simpa using fibPiSquared_coeff_eq_fib coeff rfl rfl coeff_step 0

example : coeff 4 = (75 - 28 * √5) / 250 := by
  rw [fibPiSquared_coeff_eq_fib coeff rfl rfl coeff_step 3]
  change (25 - 4 * √5) / 250 * 3 - 8 * √5 / 250 * 2 = _
  ring

end MetaMathlibExt.fibPiSquared_coeff_eq_fib

namespace MetaMathlibExt.fibPiSquared_poly_eq_sum

open Polynomial

private noncomputable def poly : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => (2 * X + C (2 * (n + 1 : ℕ) + 1 : ℤ)) * (2 * X + C (2 * (n + 1 : ℕ) + 2 : ℤ)) *
      poly (n + 1) - (X + 1) ^ 2 * (poly (n + 1)).comp (X + 1)

private theorem poly_step (n : ℕ) (hn : 1 ≤ n) :
    poly (n + 1) = (2 * X + C (2 * n + 1 : ℤ)) * (2 * X + C (2 * n + 2 : ℤ)) * poly n -
      (X + 1) ^ 2 * (poly n).comp (X + 1) := by
  cases n with
  | zero => omega
  | succ n => rfl

example : poly 2 = 3 * X ^ 2 + 12 * X + 11 := by
  rw [fibPiSquared_poly_eq_sum poly rfl poly_step (n := 2) (by decide)]
  norm_num [Finset.sum_range_succ, Finset.prod_Ico_succ_top]
  ring

example : (poly 3).eval 0 = 304 := by
  rw [fibPiSquared_poly_eq_sum poly rfl poly_step (n := 3) (by decide)]
  norm_num [Finset.sum_range_succ, Finset.prod_Ico_succ_top, Finset.prod_Icc_succ_top, Nat.choose]

end MetaMathlibExt.fibPiSquared_poly_eq_sum
