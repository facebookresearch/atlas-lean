/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.MultipleZeta.BradleyZhaoQuasiShuffle

/-! # Tests for the Bradley–Zhao quasi-shuffle product -/

open Finset PowerSeries

namespace MetaMathlibExt

private lemma coeff_one_inv_one_sub_X_pow {m : ℕ} (hm : 0 < m) :
    coeff 1 ((1 - X ^ m : ℚ⟦X⟧)⁻¹) = if 1 = m then 1 else 0 := by
  have hInv := PowerSeries.mul_inv_cancel (1 - (X : ℚ⟦X⟧) ^ m) (by simp [hm.ne'])
  rw [sub_mul, one_mul] at hInv
  have h := congrArg (fun p : ℚ⟦X⟧ => coeff 1 p) hInv
  simpa [coeff_one_mul, constantCoeff_inv, hm.ne', coeff_one, coeff_X_pow, sub_eq_zero] using h

-- Compute each term directly from its finite sum; this does not use the product theorem.
private lemma low_coefficients :
    coeff 0 (bzQMZV [2]) = 0 ∧ coeff 1 (bzQMZV [2]) = 1 ∧ coeff 2 (bzQMZV [2]) = 3 ∧
    coeff 2 (bzQMZV [2, 2]) = 0 ∧ coeff 3 (bzQMZV [2, 2]) = 1 ∧
    coeff 2 (bzQMZV [4]) = 0 ∧ coeff 3 (bzQMZV [4]) = 1 ∧
    coeff 2 (bzQMZV [3]) = 1 ∧ coeff 3 (bzQMZV [3]) = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [coeff_bzQMZV_eq_coeff_partial _ (by decide) (M := 4) (by decide)]
    norm_num [qMZVPartial.eq_1, qMZVPartial.eq_2, ← Ico_add_one_left_eq_Ioo,
      sum_Ico_eq_sum_range, sum_range_succ, ← pow_mul, mul_assoc, coeff_X_pow_mul',
      coeff_one_pow, coeff_one_mul, coeff_zero_eq_constantCoeff, constantCoeff_inv,
      coeff_one_inv_one_sub_X_pow]
  all_goals
    rw [← PowerSeries.inv_pow, coeff_one_pow]
    have h : coeff 1 ((1 - X : ℚ⟦X⟧)⁻¹) = 1 := by
      simpa using coeff_one_inv_one_sub_X_pow (m := 1) (by decide)
    norm_num [h, constantCoeff_inv]

-- Both interleavings contribute; the two merged letters have different weights.
private lemma shuffle_two_two : quasiShuffle (fun a b : ℕ => [a + b, a + b - 1]) [2] [2] =
    [[2, 2], [2, 2], [4], [3]] := by
  norm_num [quasiShuffle.eq_1, quasiShuffle.eq_2, quasiShuffle.eq_3]

example : coeff 2 (bzQMZV [2] * bzQMZV [2]) = 1 ∧
    coeff 3 (bzQMZV [2] * bzQMZV [2]) = 6 := by
  obtain ⟨h₀, h₁, h₂, _⟩ := low_coefficients
  constructor <;> rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;>
    norm_num [sum_range_succ, h₀, h₁, h₂]

example : coeff 2 (bzQMZV [2, 2] + bzQMZV [2, 2] + bzQMZV [4] + bzQMZV [3]) = 1 ∧
    coeff 3 (bzQMZV [2, 2] + bzQMZV [2, 2] + bzQMZV [4] + bzQMZV [3]) = 6 := by
  obtain ⟨_, _, _, h₂₂, h₂₃, h₄₂, h₄₃, h₃₂, h₃₃⟩ := low_coefficients
  constructor <;> norm_num [h₂₂, h₂₃, h₄₂, h₄₃, h₃₂, h₃₃]

example : bzQMZV [] = 1 := by
  ext N
  rw [coeff_bzQMZV_eq_coeff_partial [] (by simp) (Nat.lt_succ_self N)]
  rw [List.map_nil, qMZVPartial.eq_1]

example : quasiShuffle (fun a b : ℕ => [a + b, a + b - 1]) [] [2] = [[2]] ∧
    quasiShuffle (fun a b : ℕ => [a + b, a + b - 1]) [2] [] = [[2]] := by
  simp [quasiShuffle.eq_1, quasiShuffle.eq_2]

-- The public theorem rewrites multiplication to the explicit list of summands.
example : bzQMZV [2] * bzQMZV [2] = bzQMZV [2, 2] + bzQMZV [2, 2] + bzQMZV [4] + bzQMZV [3] := by
  rw [bzQMZV_mul_eq_sum_quasiShuffle [2] [2] (by decide) (by decide) (by decide) (by decide),
    shuffle_two_two]
  simp [add_assoc]

end MetaMathlibExt
