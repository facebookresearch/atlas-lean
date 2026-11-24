/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.ScheffeL1Convergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.Positivity

open Filter MeasureTheory Set
open MathlibExt.MeasureTheory.ScheffeL1ConvergenceWanted
open scoped ENNReal Topology

private noncomputable def f : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator fun _ => -2

private noncomputable def scale (n : ℕ) : ℝ := 1 + ((n + 1 : ℕ) : ℝ)⁻¹

-- A nonconstant sequence of negative functions converges to a nonzero limit.
example : Tendsto (fun n : ℕ => ∫ x : ℝ, |scale n * f x - f x|) atTop (𝓝 0) := by
  have hf : Integrable f := memLp_one_iff_integrable.mp <|
    memLp_indicator_const 1 measurableSet_Icc.nullMeasurableSet _
      (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hscale : Tendsto scale atTop (𝓝 1) := by
    change Tendsto (fun n : ℕ => 1 + ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 1)
    simpa only [add_zero] using hinv.const_add 1
  refine tendsto_integral_abs_sub_of_ae_tendsto_of_tendsto_integral_abs f
    (fun n x => scale n * f x) hf (fun n => hf.const_mul (scale n)) ?_ ?_
  · exact Eventually.of_forall fun x => by simpa only [one_mul] using hscale.mul_const (f x)
  · have hnonneg (n : ℕ) : 0 ≤ scale n := by unfold scale; positivity
    simp_rw [abs_mul, abs_of_nonneg (hnonneg _), integral_const_mul]
    simpa only [one_mul] using hscale.mul_const (∫ x : ℝ, |f x|)
