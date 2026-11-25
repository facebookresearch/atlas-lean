/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DyadicTruncation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tests: Dyadic truncation of finite distributions
-/

@[expose] public section

open scoped BigOperators
namespace MathlibExtTest.Probability.DyadicTruncation

set_option autoImplicit false

open MathlibExt.Probability.DyadicTruncation

#print axioms sum_abs_sub_dyadicTrunc_add_leftover_le
#print axioms abs_acceptance_sub_le
#print axioms two_mul_div_two_pow_dyadicPrecision_le

/-- The uniform distribution on three points at precision `2` leaves mass `1/4`. -/
theorem dyadicLeftover_uniform_three :
    dyadicLeftover (fun _ : Fin 3 => (1 : ℝ) / 3) 2 = 1 / 4 := by
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ 2 * ((1 : ℝ) / 3) := by positivity
  have hfloor : ⌊(2 : ℝ) ^ 2 * ((1 : ℝ) / 3)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff hnn]
    norm_num
  simp only [dyadicLeftover, dyadicTrunc, Fin.sum_univ_three]
  rw [hfloor]
  norm_num

/-- A concrete precision value. -/
theorem dyadicPrecision_three_half : dyadicPrecision 3 (1 / 2) = 7 := by
  have hceil : ⌈16 * (((3 : ℕ)) : ℝ) / ((1 : ℝ) / 2)⌉₊ = 96 := by
    have h : (16 : ℝ) * (((3 : ℕ)) : ℝ) / ((1 : ℝ) / 2) = (((96 : ℕ)) : ℝ) := by norm_num
    rw [h, Nat.ceil_natCast]
  unfold dyadicPrecision
  rw [hceil]
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (show (1 : ℕ) < 2 by norm_num)]
    norm_num
  · have h6 : 6 < Nat.clog 2 96 := by
      rw [Nat.lt_clog_iff_pow_lt (show (1 : ℕ) < 2 by norm_num)]
      norm_num
    omega

/-- At precision `0` the uniform three-point distribution is rejected entirely: worst case. -/
theorem dyadicLeftover_uniform_three_zero :
    dyadicLeftover (fun _ : Fin 3 => (1 : ℝ) / 3) 0 = 1 := by
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ 0 * ((1 : ℝ) / 3) := by positivity
  have hfloor : ⌊(2 : ℝ) ^ 0 * ((1 : ℝ) / 3)⌋₊ = 0 := by
    rw [Nat.floor_eq_iff hnn]
    norm_num
  simp only [dyadicLeftover, dyadicTrunc, Fin.sum_univ_three]
  rw [hfloor]
  norm_num

/-- A point mass is truncated exactly at every precision. -/
theorem dyadicTrunc_pointMass_exact (t : ℕ) (l : Fin 1) :
    dyadicTrunc (fun _ : Fin 1 => (1 : ℝ)) t l = 1 := by
  have hcast : (2 : ℝ) ^ t = (((2 ^ t : ℕ)) : ℝ) := by simp
  have hne : (((2 ^ t : ℕ)) : ℝ) ≠ 0 := by
    have h : (2 : ℕ) ^ t ≠ 0 := pow_ne_zero t (by norm_num)
    exact_mod_cast h
  unfold dyadicTrunc
  simp only [mul_one, hcast, Nat.floor_natCast]
  exact div_self hne

end MathlibExtTest.Probability.DyadicTruncation
