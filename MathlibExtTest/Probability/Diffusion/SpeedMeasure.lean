/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Diffusion.SpeedMeasure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.NhdsWithin

/-!
# Tests for the interior-basepoint scale density, speed density, and speed measure

Constant coefficients. For `b = 0` and `a = 1` the scale density is `1` and the speed
density is `2`; the flux form with the flux `F y = 2 y`, whose derivative is
`2 = m * 1`, recovers the total mass `2` of the speed measure. For `b = 1` and `a = 2`
the scale density is an explicit exponential, and moving the basepoint from `1 / 4` to
`1 / 2` rescales it by `exp (1 / 4)`.
-/

open Real Set Filter MeasureTheory
open scoped Topology
open MathlibExt.Probability.Diffusion

@[expose] public section
namespace MathlibExtTest.Probability.Diffusion.SpeedMeasure

example : 0 < scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)
    (1 / 3) :=
  scaleDensityFrom_pos _ _ _ _

example : HasDerivAt
    (scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) 0
    (1 / 2) := by
  have hdiv : ContinuousOn
      (fun x : ℝ => (fun _ => (0 : ℝ)) x / (fun _ => (1 : ℝ)) x) (Ioo 0 1) :=
    ContinuousOn.div continuousOn_const continuousOn_const
      (fun _ _ => one_ne_zero)
  have hx : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hc : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hscale : ∀ y, scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (1 / 2) y = 1 := by
    intro y
    unfold scaleDensityFrom
    have h0 : (fun z : ℝ => 2 * (fun _ => (0 : ℝ)) z / (fun _ => (1 : ℝ)) z) =
        fun _ => (0 : ℝ) := by
      funext z
      simp
    rw [h0, intervalIntegral.integral_const, smul_zero, neg_zero,
      Real.exp_zero]
  have h := hasDerivAt_scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (1 / 2) (1 / 2) hdiv hx hc
  rw [hscale] at h
  simpa using h

/-- Flux form with `b = 0`, `a = 1`: the speed density is `2`, the flux `F y = 2 y` has
derivative `2 = m * 1` with limits `0` and `2`, so the speed measure has mass `2`. -/
example : ∫ _x, (1 : ℝ) ∂(speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (1 / 2)) = 2 := by
  have hscale : ∀ y, scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (1 / 2) y = 1 := by
    intro y
    unfold scaleDensityFrom
    have h0 : (fun z : ℝ => 2 * (fun _ => (0 : ℝ)) z / (fun _ => (1 : ℝ)) z) =
        fun _ => (0 : ℝ) := by
      funext z
      simp
    rw [h0, intervalIntegral.integral_const, smul_zero, neg_zero,
      Real.exp_zero]
  have hspeed : ∀ x, speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (1 / 2) x = 2 := by
    intro x
    unfold speedDensityFrom
    rw [hscale x]
    norm_num
  have hmeas : speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) =
      (volume.restrict (Ioo (0 : ℝ) 1)).withDensity
        (fun _ => ENNReal.ofReal 2) := by
    unfold speedMeasureFrom
    apply withDensity_congr_ae
    filter_upwards with x
    rw [hspeed x]
  have hdiv : ContinuousOn
      (fun x : ℝ => (fun _ => (0 : ℝ)) x / (fun _ => (1 : ℝ)) x) (Ioo 0 1) :=
    ContinuousOn.div continuousOn_const continuousOn_const
      (fun _ _ => one_ne_zero)
  have hc : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hF : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y : ℝ => 2 * y)
      (speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) x * 1) x := by
    intro x _
    rw [hspeed x, mul_one]
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have h0 : Tendsto (fun y : ℝ => 2 * y) (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun y : ℝ => 2 * y) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun y : ℝ => 2 * y) (𝓝[<] 1) (𝓝 2) := by
    have hcont : ContinuousAt (fun y : ℝ => 2 * y) 1 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hint : Integrable (fun _ : ℝ => (1 : ℝ))
      (speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) := by
    rw [hmeas]
    have hDae : AEMeasurable (fun _ => ENNReal.ofReal 2)
        (volume.restrict (Ioo (0 : ℝ) 1)) := aemeasurable_const
    have hflt : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        ENNReal.ofReal 2 < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    rw [integrable_withDensity_iff_integrable_smul₀' hDae hflt]
    have hfin : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by
      rw [Measure.restrict_apply_univ, Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top⟩
    simp only [ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 by norm_num), smul_eq_mul,
      mul_one]
    rw [integrable_const_iff]
    exact Or.inr hfin
  have hmain := integral_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun y : ℝ => 2 * y)
    (1 / 2) 0 2 (fun _ _ => zero_lt_one) continuousOn_const hdiv hc hF h0 h1 hint
  simpa using hmain

example : scaleDensityFrom (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ)) (1 / 2)
    (1 / 3) = Real.exp (1 / 6) := by
  unfold scaleDensityFrom
  have h1 : (fun z : ℝ => 2 * (fun _ => (1 : ℝ)) z / (fun _ => (2 : ℝ)) z) =
      fun _ => (1 : ℝ) := by
    funext z
    norm_num
  rw [h1, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  congr 1
  norm_num

example : scaleDensityFrom (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ)) (1 / 2)
    (1 / 3) = Real.exp (1 / 4) * scaleDensityFrom (fun _ => (1 : ℝ))
    (fun _ => (2 : ℝ)) (1 / 4) (1 / 3) := by
  have h1 : (fun z : ℝ => 2 * (fun _ => (1 : ℝ)) z / (fun _ => (2 : ℝ)) z) =
      fun _ => (1 : ℝ) := by
    funext z
    norm_num
  have hL : scaleDensityFrom (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ)) (1 / 2)
      (1 / 3) = Real.exp (1 / 6 : ℝ) := by
    unfold scaleDensityFrom
    rw [h1, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    congr 1
    norm_num
  have hR : scaleDensityFrom (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ)) (1 / 4)
      (1 / 3) = Real.exp (-(1 / 12 : ℝ)) := by
    unfold scaleDensityFrom
    rw [h1, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    congr 1
    norm_num
  rw [hL, hR, ← Real.exp_add]
  congr 1
  norm_num

example : speedDensityFrom (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ)) (1 / 2)
    (1 / 3) = (Real.exp (1 / 6))⁻¹ := by
  have h1 : (fun z : ℝ => 2 * (fun _ => (1 : ℝ)) z / (fun _ => (2 : ℝ)) z) =
      fun _ => (1 : ℝ) := by
    funext z
    norm_num
  have hscale : scaleDensityFrom (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ)) (1 / 2)
      (1 / 3) = Real.exp (1 / 6 : ℝ) := by
    unfold scaleDensityFrom
    rw [h1, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    congr 1
    norm_num
  have hexp : Real.exp (1 / 6 : ℝ) ≠ 0 := Real.exp_ne_zero _
  unfold speedDensityFrom
  rw [hscale]
  field_simp

#print axioms scaleDensityFrom_pos
#print axioms hasDerivAt_scaleDensityFrom
#print axioms speedDensityFrom_pos
#print axioms integral_speedMeasureFrom_eq_sub_of_hasDerivAt_of_tendsto

end MathlibExtTest.Probability.Diffusion.SpeedMeasure
