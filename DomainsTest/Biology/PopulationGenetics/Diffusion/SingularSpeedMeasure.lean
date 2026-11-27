/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.OrderClosed

open Real Set Filter MeasureTheory
open scoped Topology
open MathlibExt.Biology.PopulationGenetics.Diffusion

@[expose] public section
namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure

example : ∫ x, diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun x : ℝ => x ^ 2) x ∂(speedMeasureFrom (fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ)) (1 / 2)) = 2 := by
  have h1 : ∀ y, deriv (fun x : ℝ => x ^ 2) y = 2 * y := by
    intro y
    have h := (hasDerivAt_id y).pow 2
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat, mul_one] at h
    have hg : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := h
    exact hg.deriv
  have h2 : ∀ x, deriv (deriv (fun x : ℝ => x ^ 2)) x = 2 := by
    intro x
    have hfun : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := funext h1
    rw [hfun]
    have h := (hasDerivAt_id x).const_mul 2
    rw [mul_one] at h
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 x := h
    exact hlin.deriv
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
  have hgen : diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x : ℝ => x ^ 2) = fun _ => (1 : ℝ) := by
    funext x
    unfold diffusionGenerator
    simp only [h1 x, h2 x]
    ring
  have hmeas : speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) =
      (volume.restrict (Ioo (0 : ℝ) 1)).withDensity
        (fun _ => ENNReal.ofReal 2) := by
    unfold speedMeasureFrom
    apply withDensity_congr_ae
    filter_upwards with x
    rw [hspeed x]
  have ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < (fun _ => (1 : ℝ)) x :=
    fun x _ => zero_lt_one
  have ha_cont : ContinuousOn (fun _ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const
  have hdiv : ContinuousOn
      (fun x : ℝ => (fun _ => (0 : ℝ)) x / (fun _ => (1 : ℝ)) x) (Ioo 0 1) :=
    ContinuousOn.div continuousOn_const continuousOn_const
      (fun _ _ => one_ne_zero)
  have hc : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => x ^ 2) (Icc 0 1) :=
    (contDiff_id.pow 2).contDiffOn
  have hflux : (fun y => deriv (fun x : ℝ => x ^ 2) y /
      scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y) =
      fun y => 2 * y := by
    funext y
    rw [h1 y, hscale y, div_one]
  have h0 : Tendsto (fun y => deriv (fun x : ℝ => x ^ 2) y /
      scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y)
      (𝓝[>] 0) (𝓝 0) := by
    rw [hflux]
    have hcont : ContinuousAt (fun y : ℝ => 2 * y) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h1lim : Tendsto (fun y => deriv (fun x : ℝ => x ^ 2) y /
      scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y)
      (𝓝[<] 1) (𝓝 2) := by
    rw [hflux]
    have hcont : ContinuousAt (fun y : ℝ => 2 * y) 1 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hint : Integrable
      (diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
        (fun x : ℝ => x ^ 2))
      (speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) := by
    rw [hgen, hmeas]
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
  have hmain := integral_diffusionGenerator_speedMeasureFrom
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun x : ℝ => x ^ 2) (1 / 2) 0 2
    ha_pos ha_cont hdiv hc hf h0 h1lim hint
  simpa using hmain

example : ∫ x, diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) x ∂(speedMeasureFrom
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) = 0 := by
  have hderiv4 : ∀ y, deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) y =
      2 * y * (1 - y) ^ 2 + y ^ 2 * (-2 * (1 - y)) := by
    intro y
    have hg : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
      have h := (hasDerivAt_id y).pow 2
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat,
        mul_one] at h
      exact h
    have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) y := by
      have h := (hasDerivAt_const y 1).sub (hasDerivAt_id y)
      rw [zero_sub] at h
      exact h
    have htmp := hg.mul (hsub.pow 2)
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat] at htmp
    have hmul : HasDerivAt (fun x : ℝ => x ^ 2 * (1 - x) ^ 2)
        (2 * y * (1 - y) ^ 2 + y ^ 2 * (2 * (1 - y) * -1)) y := htmp
    have h := hmul.deriv
    linear_combination h
  have hderiv2 : ∀ x, deriv (deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2)) x =
      12 * x ^ 2 - 12 * x + 2 := by
    intro x
    have hf1 : deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) =
        fun y => 2 * y * (1 - y) ^ 2 + y ^ 2 * (-2 * (1 - y)) :=
      funext hderiv4
    rw [hf1]
    have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      have h := (hasDerivAt_const x 1).sub (hasDerivAt_id x)
      rw [zero_sub] at h
      exact h
    have hA : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      have h := (hasDerivAt_id x).const_mul 2
      rw [mul_one] at h
      exact h
    have hB : HasDerivAt (fun y : ℝ => (1 - y) ^ 2) (2 * (1 - x) * -1) x := by
      have h := hsub.pow 2
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat] at h
      exact h
    have hC : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      have h := (hasDerivAt_id x).pow 2
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat,
        mul_one] at h
      exact h
    have hD : HasDerivAt (fun y : ℝ => -2 * (1 - y)) (-2 * -1) x :=
      hsub.const_mul (-2)
    have hAB : HasDerivAt (fun y : ℝ => 2 * y * (1 - y) ^ 2)
        (2 * (1 - x) ^ 2 + 2 * x * (2 * (1 - x) * -1)) x := hA.mul hB
    have hCD : HasDerivAt (fun y : ℝ => y ^ 2 * (-2 * (1 - y)))
        (2 * x * (-2 * (1 - x)) + x ^ 2 * (-2 * -1)) x := hC.mul hD
    have hP1 : HasDerivAt
        (fun y : ℝ => 2 * y * (1 - y) ^ 2 + y ^ 2 * (-2 * (1 - y)))
        ((2 * (1 - x) ^ 2 + 2 * x * (2 * (1 - x) * -1)) +
          (2 * x * (-2 * (1 - x)) + x ^ 2 * (-2 * -1))) x := hAB.add hCD
    have h := hP1.deriv
    linear_combination h
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
  have hgen : diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) =
      fun x => 6 * x ^ 2 - 6 * x + 1 := by
    funext x
    unfold diffusionGenerator
    simp only [hderiv4 x, hderiv2 x]
    ring
  have hmeas : speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) =
      (volume.restrict (Ioo (0 : ℝ) 1)).withDensity
        (fun _ => ENNReal.ofReal 2) := by
    unfold speedMeasureFrom
    apply withDensity_congr_ae
    filter_upwards with x
    rw [hspeed x]
  have ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < (fun _ => (1 : ℝ)) x :=
    fun x _ => zero_lt_one
  have ha_cont : ContinuousOn (fun _ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const
  have hdiv : ContinuousOn
      (fun x : ℝ => (fun _ => (0 : ℝ)) x / (fun _ => (1 : ℝ)) x) (Ioo 0 1) :=
    ContinuousOn.div continuousOn_const continuousOn_const
      (fun _ _ => one_ne_zero)
  have hc : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) (Icc 0 1) :=
    ((contDiff_id.pow 2).mul
      ((contDiff_const.sub contDiff_id).pow 2)).contDiffOn
  have hflux : (fun y => deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) y /
      scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y) =
      fun y => 2 * y * (1 - y) ^ 2 + y ^ 2 * (-2 * (1 - y)) := by
    funext y
    rw [hderiv4 y, hscale y, div_one]
  have h0 : Tendsto (fun y => deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) y /
      scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y)
      (𝓝[>] 0) (𝓝 0) := by
    rw [hflux]
    have hcont : ContinuousAt
        (fun y : ℝ => 2 * y * (1 - y) ^ 2 + y ^ 2 * (-2 * (1 - y))) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun y => deriv (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) y /
      scaleDensityFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2) y)
      (𝓝[<] 1) (𝓝 0) := by
    rw [hflux]
    have hcont : ContinuousAt
        (fun y : ℝ => 2 * y * (1 - y) ^ 2 + y ^ 2 * (-2 * (1 - y))) 1 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hint : Integrable
      (diffusionGenerator (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
        (fun x : ℝ => x ^ 2 * (1 - x) ^ 2))
      (speedMeasureFrom (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (1 / 2)) := by
    rw [hgen, hmeas]
    have hDae : AEMeasurable (fun _ => ENNReal.ofReal 2)
        (volume.restrict (Ioo (0 : ℝ) 1)) := aemeasurable_const
    have hflt : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        ENNReal.ofReal 2 < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    rw [integrable_withDensity_iff_integrable_smul₀' hDae hflt]
    simp only [ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 by norm_num)]
    have hfin : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by
      rw [Measure.restrict_apply_univ, Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top⟩
    have h26 : Integrable (fun _ => (26 : ℝ))
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
      rw [integrable_const_iff]
      exact Or.inr hfin
    have hcont : Continuous
        (fun x : ℝ => (2 : ℝ) • (6 * x ^ 2 - 6 * x + 1)) := by
      have hfun : Continuous (fun x : ℝ => 2 * (6 * x ^ 2 - 6 * x + 1)) := by
        fun_prop
      simpa only [smul_eq_mul] using hfun
    have haesm : AEStronglyMeasurable
        (fun x : ℝ => (2 : ℝ) • (6 * x ^ 2 - 6 * x + 1))
        (volume.restrict (Ioo (0 : ℝ) 1)) :=
      hcont.aestronglyMeasurable
    have hbd : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        ‖(2 : ℝ) • (6 * x ^ 2 - 6 * x + 1)‖ ≤ (26 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hax : |x| ≤ (1 : ℝ) := by
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2]
      have hx2le : x ^ 2 ≤ (1 : ℝ) := by
        rw [← sq_abs]
        exact pow_le_one₀ (abs_nonneg x) hax
      rw [smul_eq_mul, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hx2le, sq_nonneg (x : ℝ), hx.1, hx.2]
    exact h26.mono' haesm hbd
  exact integral_diffusionGenerator_speedMeasureFrom_eq_zero
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun x : ℝ => x ^ 2 * (1 - x) ^ 2) (1 / 2) ha_pos ha_cont hdiv hc hf h0 h1
    hint

#print axioms diffusionGenerator_eq_one_div_speedDensityFrom
#print axioms integral_diffusionGenerator_speedMeasureFrom
#print axioms integral_diffusionGenerator_speedMeasureFrom_eq_zero

example : 0 < speedDensityFrom
    (fun x : ℝ => (1 * (1 - x) - 1 * x) / 2)
    (fun x : ℝ => x * (1 - x)) (1 / 2) (1 / 3) := by
  have ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < (fun x : ℝ => x * (1 - x)) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    exact mul_pos hx0 (sub_pos.mpr hx1)
  have hx : (1 / 3 : ℝ) ∈ Ioo 0 1 := by norm_num
  exact speedDensityFrom_pos _ _ _ _ ha_pos hx

example : HasDerivAt
    (scaleDensityFrom (fun x : ℝ => (1 * (1 - x) - 1 * x) / 2)
      (fun x : ℝ => x * (1 - x)) (1 / 2)) 0 (1 / 2) := by
  have hb_cont : Continuous (fun x : ℝ => (1 * (1 - x) - 1 * x) / 2) := by
    fun_prop
  have ha_cont : Continuous (fun x : ℝ => x * (1 - x)) := by
    fun_prop
  have hne : ∀ x ∈ Ioo (0 : ℝ) 1, (fun x : ℝ => x * (1 - x)) x ≠ 0 := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    exact mul_ne_zero (ne_of_gt hx0) (ne_of_gt (sub_pos.mpr hx1))
  have hdiv : ContinuousOn (fun x : ℝ => (fun x : ℝ => (1 * (1 - x) - 1 * x) / 2) x /
      (fun x : ℝ => x * (1 - x)) x) (Ioo 0 1) :=
    hb_cont.continuousOn.div ha_cont.continuousOn hne
  have hx : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hc : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have h := hasDerivAt_scaleDensityFrom (fun x : ℝ => (1 * (1 - x) - 1 * x) / 2)
    (fun x : ℝ => x * (1 - x)) (1 / 2) (1 / 2) hdiv hx hc
  have hb : (1 * (1 - (1 / 2 : ℝ)) - 1 * (1 / 2)) / 2 = 0 := by
    norm_num
  rw [hb] at h
  simpa using h

/-! ### Positive-mutation Wright–Fisher diffusion: singular endpoints

Mutation rates `θ₁ = 2` and `θ₂ = 1`: drift `b x = (2 (1 - x) - x) / 2` and variance
`a x = x (1 - x)`, so `2 b / a = 2 / x - 1 / (1 - x)` and `b / a` is not integrable at the
endpoints. Normalized at `1 / 2`, the scale density is `1 / (8 x² (1 - x))` and the speed
density is `16 x` on `(0, 1)`. For `f x = x` both boundary fluxes `f' / s = 8 x² (1 - x)`
vanish, and the generator `L f = b` integrates to zero against the speed measure. -/

/-- The drift-to-variance ratio of the example is not interval integrable on `[0, 1]`. -/
theorem not_intervalIntegrable_wfMutation_div : ¬ IntervalIntegrable
    (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2 / (x * (1 - x))) volume 0 1 := by
  intro h
  have h4 : IntervalIntegrable
      (fun x : ℝ => 4 * ((2 * (1 - x) - 1 * x) / 2 / (x * (1 - x)))) volume 0 (1 / 2) := by
    refine (h.mono_set ?_).const_mul 4
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), uIcc_of_le zero_le_one]
    exact Icc_subset_Icc_right (by norm_num)
  have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 (1 / 2) := by
    refine h4.mono_fun measurable_inv.aestronglyMeasurable ?_
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hnum : 0 ≤ (2 * (1 - x) - 1 * x) / 2 := by linarith [hx.2]
    have hkey : 4 * ((2 * (1 - x) - 1 * x) / 2 / (x * (1 - x))) - x⁻¹ =
        (3 - 5 * x) / (x * (1 - x)) := by
      field_simp
      ring
    have hgap : 0 ≤ (3 - 5 * x) / (x * (1 - x)) :=
      div_nonneg (by linarith [hx.2]) (mul_pos hx0 hx1).le
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hx0.le),
      Real.norm_of_nonneg (mul_nonneg (by norm_num) (div_nonneg hnum (mul_pos hx0 hx1).le))]
    linarith
  rcases intervalIntegrable_inv_iff.mp hinv with h0 | h0
  · norm_num at h0
  · exact h0 left_mem_uIcc

/-- The example is not a regular diffusion in the sense of `IsRegularDiffusion`. -/
example : ¬ IsRegularDiffusion (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2)
    (fun x : ℝ => x * (1 - x)) :=
  fun h => not_intervalIntegrable_wfMutation_div h.intervalIntegrable_div

/-- Closed form of the scale density of the example, normalized at `1 / 2`. -/
theorem wfMutation_scaleDensityFrom {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    scaleDensityFrom (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2) (fun x : ℝ => x * (1 - x))
      (1 / 2) y = 1 / (8 * (y ^ 2 * (1 - y))) := by
  have hderiv : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun z : ℝ => Real.log (z ^ 2 * (1 - z)))
      (2 * ((2 * (1 - z) - 1 * z) / 2) / (z * (1 - z))) z := by
    intro z hz
    have hz0 : z ≠ 0 := hz.1.ne'
    have hz1 : 1 - z ≠ 0 := (sub_pos.mpr hz.2).ne'
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have hs : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (1 : ℝ)
    have hprod : HasDerivAt (fun x : ℝ => x ^ 2 * (1 - x)) (2 * z * (1 - z) + z ^ 2 * -1) z :=
      hp.mul hs
    convert hprod.log (mul_ne_zero (pow_ne_zero 2 hz0) hz1) using 1
    field_simp
    ring
  have hsub : ∀ z ∈ uIcc (1 / 2 : ℝ) y, z ∈ Ioo (0 : ℝ) 1 := by
    intro z hz
    rcases Set.mem_uIcc.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith [hy.2]⟩
    · exact ⟨by linarith [hy.1], by linarith⟩
  have hint : IntervalIntegrable
      (fun z : ℝ => 2 * ((2 * (1 - z) - 1 * z) / 2) / (z * (1 - z))) volume (1 / 2) y :=
    ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun z hz => mul_ne_zero (hsub z hz).1.ne' (sub_pos.mpr (hsub z hz).2).ne')
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z hz => hderiv z (hsub z hz)) hint
  have hy2 : 0 < y ^ 2 * (1 - y) := mul_pos (pow_pos hy.1 2) (sub_pos.mpr hy.2)
  simp only [scaleDensityFrom]
  rw [hI, neg_sub, Real.exp_sub, Real.exp_log hy2,
    Real.exp_log (show (0 : ℝ) < (1 / 2) ^ 2 * (1 - 1 / 2) by norm_num)]
  field_simp
  norm_num

/-- The speed density of the example, normalized at `1 / 2`, is `16 x` on `(0, 1)`. -/
theorem wfMutation_speedDensityFrom {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    speedDensityFrom (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2) (fun x : ℝ => x * (1 - x))
      (1 / 2) x = 16 * x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  simp only [speedDensityFrom]
  rw [wfMutation_scaleDensityFrom hx]
  field_simp
  ring

/-- The speed measure of the example is `16 x dx` on `(0, 1)`. -/
theorem wfMutation_speedMeasureFrom :
    speedMeasureFrom (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2) (fun x : ℝ => x * (1 - x))
      (1 / 2) =
      (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (16 * x)) := by
  simp only [speedMeasureFrom]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [wfMutation_speedDensityFrom hx]

/-- The flux `f' / s` of `f x = x` is `8 x² (1 - x)` on `(0, 1)`. -/
theorem wfMutation_flux_eqOn :
    EqOn (fun y => deriv (fun x : ℝ => x) y / scaleDensityFrom
        (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2) (fun x : ℝ => x * (1 - x)) (1 / 2) y)
      (fun y => 8 * (y ^ 2 * (1 - y))) (Ioo 0 1) := fun y hy => by
  simp only [deriv_id'', wfMutation_scaleDensityFrom hy, one_div_one_div]

/-- The flux of `f x = x` vanishes at the left endpoint. -/
theorem wfMutation_tendsto_flux_zero :
    Tendsto (fun y => deriv (fun x : ℝ => x) y / scaleDensityFrom
        (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2) (fun x : ℝ => x * (1 - x)) (1 / 2) y)
      (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => 8 * (y ^ 2 * (1 - y))) (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun y : ℝ => 8 * (y ^ 2 * (1 - y))) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
  exact (wfMutation_flux_eqOn hy).symm

/-- The flux of `f x = x` vanishes at the right endpoint. -/
theorem wfMutation_tendsto_flux_one :
    Tendsto (fun y => deriv (fun x : ℝ => x) y / scaleDensityFrom
        (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2) (fun x : ℝ => x * (1 - x)) (1 / 2) y)
      (𝓝[<] 1) (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => 8 * (y ^ 2 * (1 - y))) (𝓝[<] 1) (𝓝 0) := by
    have hcont : ContinuousAt (fun y : ℝ => 8 * (y ^ 2 * (1 - y))) 1 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with y hy
  exact (wfMutation_flux_eqOn hy).symm

/-- The generator of the example applied to `f x = x` is the drift. -/
theorem wfMutation_diffusionGenerator_id (x : ℝ) :
    diffusionGenerator (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2) (fun x : ℝ => x * (1 - x))
      (fun x : ℝ => x) x = (2 * (1 - x) - 1 * x) / 2 := by
  simp only [diffusionGenerator, deriv_id'', deriv_const', mul_zero, zero_add, mul_one]

/-- The generator of `f x = x` is integrable against the speed measure of the example. -/
theorem wfMutation_integrable :
    Integrable (diffusionGenerator (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2)
        (fun x : ℝ => x * (1 - x)) (fun x : ℝ => x))
      (speedMeasureFrom (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2) (fun x : ℝ => x * (1 - x))
        (1 / 2)) := by
  have hDae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (16 * x))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)).aemeasurable
  rw [wfMutation_speedMeasureFrom, integrable_withDensity_iff_integrable_smul₀' hDae
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hc : Integrable (fun x : ℝ => 16 * x * ((2 * (1 - x) - 1 * x) / 2))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((by fun_prop : Continuous fun x : ℝ => 16 * x * ((2 * (1 - x) - 1 * x) / 2)).integrableOn_Icc
      (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
  refine hc.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 16 * x by linarith [hx.1]), smul_eq_mul,
    wfMutation_diffusionGenerator_id]

/-- Weak stationarity in the singular case, through the zero-flux corollary: the generator
of `f x = x` integrates to zero against the speed measure `16 x dx` on `(0, 1)`. -/
example : ∫ x, diffusionGenerator (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2)
    (fun x : ℝ => x * (1 - x)) (fun x : ℝ => x) x ∂(speedMeasureFrom
      (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2) (fun x : ℝ => x * (1 - x)) (1 / 2)) = 0 := by
  have ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < (fun x : ℝ => x * (1 - x)) x :=
    fun x hx => mul_pos hx.1 (sub_pos.mpr hx.2)
  have ha_cont : ContinuousOn (fun x : ℝ => x * (1 - x)) (Ioo 0 1) := by fun_prop
  have hdiv : ContinuousOn (fun x : ℝ => (fun x : ℝ => (2 * (1 - x) - 1 * x) / 2) x /
      (fun x : ℝ => x * (1 - x)) x) (Ioo 0 1) :=
    ContinuousOn.div (by fun_prop) ha_cont fun x hx => (ha_pos x hx).ne'
  have hc : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => x) (Icc 0 1) := contDiff_id.contDiffOn
  exact integral_diffusionGenerator_speedMeasureFrom_eq_zero _ _ _ _ ha_pos ha_cont hdiv hc hf
    wfMutation_tendsto_flux_zero wfMutation_tendsto_flux_one wfMutation_integrable

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure
