/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FareyStaircase
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Tests for Farey staircases and harmonic blocks -/

open Filter MetaMathlibExt

example (x : ℝ) : fareyZoom 0 x = 0 := by simp [fareyZoom]

-- The first two lower approximations of 3/4 are 0 and 1/2.
example : fareyZoom 2 (3 / 2) = 1 / 2 := by
  rw [fareyZoom_eq_sum (by decide), Finset.sum_Icc_succ_top (by decide)]
  norm_num

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
