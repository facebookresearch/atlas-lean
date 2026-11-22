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
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.NhdsWithin

open Real Set Filter MeasureTheory
open scoped Topology
open MathlibExt.Biology.PopulationGenetics.Diffusion

@[expose] public section
namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure

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

#print axioms hasDerivAt_scaleDensityFrom
#print axioms diffusionGenerator_eq_one_div_speedDensityFrom
#print axioms integral_diffusionGenerator_speedMeasureFrom
#print axioms integral_diffusionGenerator_speedMeasureFrom_eq_zero

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure
