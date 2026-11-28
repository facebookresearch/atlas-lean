/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FareyStaircase
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Tests for Farey staircases and harmonic blocks -/

open Filter MetaMathlibExt

example (x : ℝ) : fareyZoom 0 x = 0 := by simp [fareyZoom]

-- The first two lower approximations of 3/4 are 0 and 1/2.
example : fareyZoom 2 (3 / 2) = 1 / 2 := by
  rw [fareyZoom_eq_sum (by decide), Finset.sum_Icc_succ_top (by decide)]
  norm_num

-- At the first admissible order, the lower approximation jumps from -1 to -1/2.
example : fareyStaircase 2 (-1 / 2) - fareyStaircase 1 (-1 / 2) = 1 / 4 := by
  rw [(fareyStaircase_sub_eq (n := 2) (by decide) _).1]
  norm_num [fareyStaircase_one]

-- At 1/3 the first two approximations vanish and the third floor is exactly one.
example : fareyStaircase 3 (1 / 3) = 1 / 9 := by
  have h₂ : fareyStaircase 2 (1 / 3) = 0 := by
    rw [fareyStaircase, Finset.sum_Icc_succ_top (by decide)]
    norm_num
  have h := (fareyStaircase_sub_eq (n := 3) (by decide) (1 / 3)).2
  norm_num [h₂] at h
  linarith

-- A singleton block leaves exactly its reciprocal, including at the initial index zero.
example : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
  simpa using tendsto_harmonic_block_sub_integral (a := id) (b := id) (fun _ => le_rfl) tendsto_id

-- The integral on a positive dyadic block is constant, so the block sum tends to log 2.
example : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc n (2 * n), (1 / k : ℝ))
    atTop (nhds (Real.log 2)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply (tendsto_harmonic_block_sub_integral (a := id) (b := fun n => 2 * n)
    (fun n => Nat.le_mul_of_pos_left n (by decide)) tendsto_id).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp [integral_inv_of_pos, hn', Nat.cast_mul, ne_of_gt hn']

-- At zero there are no positive floor levels.
example : Tendsto (fun n : ℕ => fareyZoom n 0) atTop (nhds 0) := by
  simpa using tendsto_fareyZoom (x := 0) le_rfl

-- At x = 2 the top level is included, and its logarithm is zero.
example : Tendsto (fun n : ℕ => fareyZoom n 2) atTop (nhds (Real.log 2)) := by
  have h := tendsto_fareyZoom (x := 2) (by norm_num)
  have hset : Finset.Icc 1 ⌊(2 : ℝ)⌋₊ = {1, 2} := by norm_num; decide
  rw [hset] at h
  convert h using 2
  norm_num

-- Below the first step the sum of logarithmic contributions is empty.
example {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 *
      (fareyStaircase n (x / n) - fareyStaircase (n - 1) (x / n))) atTop (nhds 0) := by
  simpa [Nat.floor_eq_zero.mpr hx₁] using tendsto_sq_mul_fareyStaircase_sub hx

-- At x = 2 the upper endpoint contributes one, even though its logarithm vanishes.
example : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 *
    (fareyStaircase n (2 / n) - fareyStaircase (n - 1) (2 / n))) atTop
    (nhds (2 - Real.log 2)) := by
  have h := tendsto_sq_mul_fareyStaircase_sub (x := 2) (by norm_num)
  have hset : Finset.Icc 1 ⌊(2 : ℝ)⌋₊ = {1, 2} := by norm_num; decide
  rw [hset] at h
  convert h using 2
  norm_num

-- At the origin the limit is the negative of the function value.
example {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0) :
    Tendsto (fun l : ℝ => (l⁻¹ * f 0 - f 0) / (l - 1)) (nhdsWithin 1 {1}ᶜ)
      (nhds (-f 0)) := by
  simpa using tendsto_dilation_quotient hf

-- The dilation derivative of the square function is the square function itself.
example (x : ℝ) :
    Tendsto (fun l : ℝ => (l⁻¹ * (l * x) ^ 2 - x ^ 2) / (l - 1)) (nhdsWithin 1 {1}ᶜ)
      (nhds (x ^ 2)) := by
  convert tendsto_dilation_quotient (hasDerivAt_pow 2 x) using 2
  push_cast
  ring
