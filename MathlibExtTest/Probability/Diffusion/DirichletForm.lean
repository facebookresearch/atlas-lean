/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Diffusion.DirichletForm
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.NhdsWithin

/-!
# Tests for integration by parts against the interior-basepoint speed measure

Constant coefficients `b = 0`, `a = 1` and basepoint `1 / 2`: the scale density is `1` and the
speed density is `2`. With `f x = x`, `h = 1` and `Q y = 2 y`, so that `Q' = 2 = m * h`, the
boundary term is `f 1 * Q 1 - f 0 * Q 0 = 2` and `∫₀¹ f' * Q = 1`, so the identity evaluates
`∫ x d(speed measure)` to `1`.
-/

open Set Filter MeasureTheory
open scoped Topology
open MathlibExt.Probability.Diffusion

@[expose] public section
namespace MathlibExtTest.Probability.Diffusion.DirichletForm

example : ∫ x, x * 1 ∂(speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) = 1 := by
  have hscale : ∀ y, scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y = 1 := by
    intro y
    simp [scaleDensityFrom]
  have hspeed : ∀ x, speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x = 2 := by
    intro x
    simp only [speedDensityFrom, hscale, mul_one, div_one]
  have hmeas : speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) =
      (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun _ => ENNReal.ofReal 2) := by
    simp only [speedMeasureFrom, hspeed]
  have hdiv : ContinuousOn
      (fun x : ℝ => (fun _ => (0 : ℝ)) x / (fun _ => (1 : ℝ)) x) (Ioo 0 1) :=
    ContinuousOn.div continuousOn_const continuousOn_const (fun _ _ => one_ne_zero)
  have hc : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hQ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y : ℝ => 2 * y)
      (speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x * 1) x := by
    intro x _
    rw [hspeed x, mul_one]
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hB0 : Tendsto (fun y : ℝ => y * (2 * y)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun y : ℝ => y * (2 * y)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hB1 : Tendsto (fun y : ℝ => y * (2 * y)) (𝓝[<] 1) (𝓝 2) := by
    have hcont : ContinuousAt (fun y : ℝ => y * (2 * y)) 1 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hint : Integrable (fun x : ℝ => x * 1)
      (speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) := by
    rw [hmeas, integrable_withDensity_iff_integrable_smul₀' aemeasurable_const
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 by norm_num), smul_eq_mul]
    exact ((by fun_prop : Continuous fun x : ℝ => 2 * (x * 1)).integrableOn_Icc
      (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
  have hdir : IntervalIntegrable (fun x => deriv (fun x : ℝ => x) x * (2 * x)) volume 0 1 := by
    simp only [deriv_id'', one_mul]
    exact (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hmain := integral_mul_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun x : ℝ => x) (fun _ => (1 : ℝ))
    (fun y : ℝ => 2 * y) (1 / 2) 0 2 (fun _ _ => zero_lt_one) continuousOn_const hdiv hc
    differentiableOn_id hQ hB0 hB1 hint hdir
  rw [hmain]
  simp only [deriv_id'', one_mul]
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num

#print axioms integral_mul_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto

end MathlibExtTest.Probability.Diffusion.DirichletForm
