/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Integral.ExponentialKernelApproxIdentity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum

open MeasureTheory Set Filter
open scoped Topology ENNReal
open MathlibExt.MeasureTheory.ExponentialKernelApproxIdentityWanted

private noncomputable def sample : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator (fun _ => -2)

-- Compare with the explicit, nonzero squared norm of a signed interval indicator.
example : Tendsto (fun n : ℕ => (n : ℝ) *
    (∫ x : ℝ, ∫ y : ℝ, sample x * sample y * Real.exp (-2 * (n : ℝ) * |x - y|)))
    atTop (𝓝 4) := by
  have hsq : (fun x => sample x ^ (2 : ℕ)) = (Icc (0 : ℝ) 1).indicator (fun _ => 4) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [sample, hx]
    norm_num
  have hm : Measurable sample := measurable_const.indicator measurableSet_Icc
  have hfin : (volume : Measure ℝ) (Icc (0 : ℝ) 1) ≠ ∞ := isCompact_Icc.measure_lt_top.ne
  have hLp : MemLp sample 2 volume := by
    apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    rw [hsq, integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const hfin
  have hvalue : (∫ x, sample x ^ (2 : ℕ)) = 4 := by
    rw [hsq, integral_indicator measurableSet_Icc, setIntegral_const]
    norm_num [Measure.real, Real.volume_Icc]
  rw [← hvalue]
  exact tendsto_mul_integral_integral_exp_neg_two_mul_abs_sub sample hLp
