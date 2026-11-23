/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.LpSubadditivePowLtOne
import Mathlib.Tactic.NormNum

open Filter MeasureTheory Set
open MathlibExt.MeasureTheory.LpSubadditivePowLtOneWanted
open scoped ENNReal

-- Opposite-sign constants in L^(1/2) on a probability space.
example : abs ((4 : ℝ) ^ (2 : ℝ)⁻¹ - 1) ≤ (5 : ℝ) ^ (2 : ℝ)⁻¹ := by
  let μ := Measure.dirac (0 : ℝ)
  let p : ℝ≥0∞ := 2⁻¹
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hp0 : 0 < p := ENNReal.inv_pos.mpr (by simp)
  have hp1 : p < 1 := ENNReal.inv_lt_one.mpr (by norm_num)
  have hf : MemLp (fun _ : ℝ => (4 : ℝ)) p μ := memLp_const 4
  have hg : MemLp (fun _ : ℝ => (-1 : ℝ)) p μ := memLp_const (-1)
  let f := hf.toLp _
  let g := hg.toLp _
  have hf' : ∀ᵐ x ∂μ, f x = 4 := hf.coeFn_toLp
  have hg' : ∀ᵐ x ∂μ, g x = -1 := hg.coeFn_toLp
  have hl : (fun x => abs (|f x| ^ p.toReal - |g x| ^ p.toReal)) =ᵐ[μ]
      fun _ => abs ((4 : ℝ) ^ p.toReal - 1) := by
    filter_upwards [hf', hg'] with x hfx hgx
    norm_num [hfx, hgx]
  have hr : (fun x => |f x - g x| ^ p.toReal) =ᵐ[μ] fun _ => (5 : ℝ) ^ p.toReal := by
    filter_upwards [hf', hg'] with x hfx hgx
    norm_num [hfx, hgx]
  have h := integral_abs_rpow_sub_rpow_le_integral_rpow_abs_sub hp0 hp1 (f := f) (g := g)
  rw [integral_congr_ae hl, integral_congr_ae hr] at h
  simpa [integral_const, measureReal_def, p, ENNReal.toReal_inv] using h
