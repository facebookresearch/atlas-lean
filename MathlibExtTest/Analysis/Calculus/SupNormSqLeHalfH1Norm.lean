/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.SupNormSqLeHalfH1Norm
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Tests for the sup-norm bound by the H¹ energy -/

open Set MathlibExt.Analysis.Calculus.SupNormSqLeHalfH1NormWanted

-- On a singleton, vanishing at that point suffices for an arbitrary function.
example (a : ℝ) (f : ℝ → ℝ) (ha : f a = 0) :
    sSup ((fun x => ‖f x‖) '' Icc a a) ^ 2 ≤ 0 := by
  have hf : ContDiffOn ℝ 1 f (Icc a a) := by
    apply (contDiffOn_const (c := f a)).congr
    simp
  simpa only [intervalIntegral.integral_same, mul_zero] using
    sSup_norm_sq_le_half_integral_sq_add_deriv_sq le_rfl hf ha ha

-- The absolute value creates a corner at the left endpoint. The value at the midpoint
-- gives a positive lower bound for the energy in spite of that corner.
example :
    (1 / 8 : ℝ) ≤ ∫ x in (0 : ℝ)..1,
      ((|x| * (1 - x)) ^ 2 + deriv (fun t : ℝ => |t| * (1 - t)) x ^ 2) := by
  let f (t : ℝ) := |t| * (1 - t)
  have hf : ContDiffOn ℝ 1 f (Icc 0 1) := by
    apply (contDiffOn_id.mul ((contDiffOn_const (c := (1 : ℝ))).sub contDiffOn_id)).congr
    intro x hx
    simp [f, abs_of_nonneg hx.1]
  have h := sSup_norm_sq_le_half_integral_sq_add_deriv_sq zero_le_one hf (by simp [f])
    (by simp [f])
  have hmid : (1 / 2 : ℝ) ∈ Icc 0 1 := ⟨by norm_num, by norm_num⟩
  have hle := le_csSup (isCompact_Icc.bddAbove_image hf.continuousOn.norm)
    (mem_image_of_mem (fun x => ‖f x‖) hmid)
  have hs := pow_le_pow_left₀ (norm_nonneg (f (1 / 2))) hle 2
  rw [show ‖f (1 / 2)‖ = 1 / 4 by norm_num [f, Real.norm_eq_abs]] at hs
  change 1 / 8 ≤ ∫ x in (0 : ℝ)..1, (f x ^ 2 + deriv f x ^ 2)
  linarith
