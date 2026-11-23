/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.Real
public import MathlibExt.Probability.Statistics.MLEAsymptoticNormality
public import MathlibExt.Probability.Statistics.FisherInformation

/-!
# Score has mean zero under regularity

For a positive density family differentiable in `θ` everywhere, with differentiation under
the integral justified by a global integrable majorant and probability-law normalization
for every `θ`, the score integrates to zero under `p θ₀ ν`. This supplies the `hs_mean`
hypothesis assumed downstream.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MLEAsymptoticNormality

open MeasureTheory Filter Topology MathlibExt.Probability.Statistics.FisherInformation

private theorem lintegral_ofReal_p_eq_one {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} (θ : ℝ)
    (hprob : ∀ θ, IsProbabilityMeasure (lawOf ν p θ)) :
    ∫⁻ x, ENNReal.ofReal (p θ x) ∂ν = 1 := by
  have h1 : (lawOf ν p θ) Set.univ = 1 := (hprob θ).measure_univ
  rw [lawOf, withDensity_apply _ MeasurableSet.univ] at h1
  simpa using h1

/-- The density at the base point is integrable. -/
private theorem integrable_at_base {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ : ℝ}
    (hp_pos : ∀ x, 0 < p θ₀ x) (hp_meas : ∀ θ, Measurable (p θ))
    (hprob : ∀ θ, IsProbabilityMeasure (lawOf ν p θ)) :
    Integrable (p θ₀) ν := by
  have h1 := lintegral_ofReal_p_eq_one (ν := ν) (p := p) θ₀ hprob
  have hI := integrable_toReal_of_lintegral_ne_top (μ := ν)
    ((hp_meas θ₀).ennreal_ofReal.aemeasurable) (by rw [h1]; exact ENNReal.one_ne_top)
  have heq : (fun x => (ENNReal.ofReal (p θ₀ x)).toReal) = p θ₀ :=
    funext fun x => ENNReal.toReal_ofReal (hp_pos x).le
  rwa [heq] at hI

/-- Every section is integrable, via the Lipschitz bound from the global deriv majorant. -/
private theorem integrable_section {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ : ℝ} {C : 𝓧 → ℝ} (t : ℝ)
    (hp_meas : ∀ θ, Measurable (p θ))
    (hp_diff : ∀ x, ∀ θ, DifferentiableAt ℝ (fun t => p t x) θ)
    (hCint : Integrable C ν)
    (hCbound : ∀ x, ∀ t, ‖deriv (fun s => p s x) t‖ ≤ C x)
    (h0 : Integrable (p θ₀) ν) :
    Integrable (p t) ν := by
  refine integrable_of_norm_sub_le (μ := ν) (f₀ := p θ₀) (f₁ := p t)
    (g := fun x => C x * ‖t - θ₀‖) (hp_meas t).aestronglyMeasurable h0
    (hCint.mul_const _) (Eventually.of_forall fun x => ?_)
  show ‖p θ₀ x - p t x‖ ≤ C x * ‖t - θ₀‖
  have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := Set.univ)
    (f := fun s => p s x) (C := C x) (fun y _ => hp_diff x y) (fun y _ => hCbound x y)
    convex_univ (Set.mem_univ t) (Set.mem_univ θ₀)
  rw [norm_sub_rev t θ₀]
  exact hMVT

/-- The base-point density integrates to one. -/
private theorem integral_at_base_eq_one {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ : ℝ}
    (hp_pos : ∀ x, 0 < p θ₀ x)
    (hprob : ∀ θ, IsProbabilityMeasure (lawOf ν p θ))
    (h0 : Integrable (p θ₀) ν) :
    ∫ x, p θ₀ x ∂ν = 1 := by
  have h1 := lintegral_ofReal_p_eq_one (ν := ν) (p := p) θ₀ hprob
  have h2 : ENNReal.ofReal (∫ x, p θ₀ x ∂ν) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal h0
      (Eventually.of_forall fun x => (hp_pos x).le)]
    exact h1
  have hnn : 0 ≤ ∫ x, p θ₀ x ∂ν :=
    integral_nonneg_of_ae (Eventually.of_forall fun x => (hp_pos x).le)
  have h3 := congrArg ENNReal.toReal h2
  rw [ENNReal.toReal_ofReal hnn, ENNReal.toReal_one] at h3
  exact h3

/-- Every section integrates to at most one (negative parts only decrease the integral). -/
private theorem integral_section_le_one {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} (t : ℝ)
    (hp_meas : ∀ θ, Measurable (p θ))
    (hprob : ∀ θ, IsProbabilityMeasure (lawOf ν p θ))
    (hInt : Integrable (p t) ν) :
    ∫ x, p t x ∂ν ≤ 1 := by
  have hLt := lintegral_ofReal_p_eq_one (ν := ν) (p := p) t hprob
  have hI2 : Integrable (fun x => (ENNReal.ofReal (p t x)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top (μ := ν)
      ((hp_meas t).ennreal_ofReal.aemeasurable) (by rw [hLt]; exact ENNReal.one_ne_top)
  have hpt : ∀ x, p t x ≤ (ENNReal.ofReal (p t x)).toReal := by
    intro x
    by_cases h : 0 ≤ p t x
    · rw [ENNReal.toReal_ofReal h]
    · have hlt : p t x < 0 := lt_of_not_ge h
      have h0 : ENNReal.ofReal (p t x) = 0 := ENNReal.ofReal_of_nonpos (le_of_lt hlt)
      rw [h0]
      exact le_trans (le_of_lt hlt) ENNReal.toReal_nonneg
  have hmono := integral_mono hInt hI2 hpt
  have hval : ∫ x, (ENNReal.ofReal (p t x)).toReal ∂ν = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => ENNReal.toReal_nonneg) hI2.aestronglyMeasurable]
    have hcongr : ∀ x, ENNReal.ofReal ((ENNReal.ofReal (p t x)).toReal)
        = ENNReal.ofReal (p t x) :=
      fun x => ENNReal.ofReal_toReal ENNReal.ofReal_ne_top
    simp only [hcongr, hLt, ENNReal.toReal_one]
  rw [hval] at hmono
  exact hmono

/-- The `θ`-derivative sections are ae strongly measurable, as limits of difference quotients. -/
private theorem aeStronglyMeasurable_deriv_section {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ : ℝ}
    (hp_meas : ∀ θ, Measurable (p θ))
    (hp_diff : ∀ x, ∀ θ, DifferentiableAt ℝ (fun t => p t x) θ) :
    AEStronglyMeasurable (fun x => deriv (fun t => p t x) θ₀) ν := by
  apply Measurable.aestronglyMeasurable
  refine measurable_of_tendsto_metrizable
    (f := fun n x => ((n : ℝ) + 1) * (p (θ₀ + 1 / ((n : ℝ) + 1)) x - p θ₀ x)) ?_ ?_
  · intro n
    exact ((hp_meas _).sub (hp_meas _)).const_mul _
  · rw [tendsto_pi_nhds]
    intro x
    have h2 : Tendsto (fun n : ℕ => θ₀ + 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] θ₀) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have h' := h.const_add θ₀
        simpa using h'
      · apply Eventually.of_forall
        intro n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        exact ne_of_gt (by linarith)
    have h3 := (hp_diff x θ₀).hasDerivAt.tendsto_slope.comp h2
    refine Filter.Tendsto.congr' (Eventually.of_forall fun n => ?_) h3
    simp only [Function.comp_apply, slope_def_module, add_sub_cancel_left, one_div, inv_inv,
      smul_eq_mul]

/-- **Score has mean zero under regularity.** For a positive density family differentiable in `θ` everywhere, with differentiation under
the integral justified by an explicit global integrable majorant and probability-law
normalization for every `θ`, the score integrates to zero
under `p θ₀ ν`. This supplies the `hs_mean` hypothesis assumed downstream. -/
theorem integral_score_mean_zero {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ : ℝ}
    (hp_pos : ∀ x, 0 < p θ₀ x) (hp_meas : ∀ θ, Measurable (p θ))
    (hp_diff : ∀ x, ∀ θ, DifferentiableAt ℝ (fun t => p t x) θ)
    (hprob : ∀ θ, IsProbabilityMeasure (lawOf ν p θ))
    (hbound : ∃ C : 𝓧 → ℝ, Integrable C ν ∧
      ∀ x, ∀ t, ‖deriv (fun s => p s x) t‖ ≤ C x) :
    ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0 := by
  obtain ⟨C, hCint, hCbound⟩ := hbound
  have h0 : Integrable (p θ₀) ν := integrable_at_base hp_pos hp_meas hprob
  have hF'meas : AEStronglyMeasurable (fun x => deriv (fun t => p t x) θ₀) ν :=
    aeStronglyMeasurable_deriv_section hp_meas hp_diff
  have hexch : HasDerivAt (fun t => ∫ x, p t x ∂ν)
      (∫ x, deriv (fun t => p t x) θ₀ ∂ν) θ₀ := by
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := p) (x₀ := θ₀)
      (s := Set.univ) (μ := ν) (F' := fun t x => deriv (fun s => p s x) t) (bound := C)
      Filter.univ_mem
      (Eventually.of_forall fun t => (hp_meas t).aestronglyMeasurable)
      h0 hF'meas
      (Eventually.of_forall fun a t _ => hCbound a t)
      hCint
      (Eventually.of_forall fun a t _ => (hp_diff a t).hasDerivAt)
    exact key.2
  have hG1 : ∀ t, ∫ x, p t x ∂ν ≤ 1 := fun t =>
    integral_section_le_one t hp_meas hprob
      (integrable_section t hp_meas hp_diff hCint hCbound h0)
  have hG0 : ∫ x, p θ₀ x ∂ν = 1 := integral_at_base_eq_one hp_pos hprob h0
  have hmax : IsLocalMax (fun t => ∫ x, p t x ∂ν) θ₀ :=
    Eventually.of_forall fun t => by
      show ∫ x, p t x ∂ν ≤ ∫ x, p θ₀ x ∂ν
      rw [hG0]
      exact hG1 t
  have hint0 : ∫ x, deriv (fun t => p t x) θ₀ ∂ν = 0 :=
    hmax.hasDerivAt_eq_zero hexch
  rw [lawOf, integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (p θ₀ x)) (hp_meas θ₀).ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hsc : ∀ x, (ENNReal.ofReal (p θ₀ x)).toReal • score p θ₀ x
      = deriv (fun t => p t x) θ₀ := by
    intro x
    rw [ENNReal.toReal_ofReal (hp_pos x).le, smul_eq_mul]
    have hs : score p θ₀ x = deriv (fun t => p t x) θ₀ / p θ₀ x :=
      ((hp_diff x θ₀).hasDerivAt.log (hp_pos x).ne').deriv
    rw [hs]
    have hne := (hp_pos x).ne'
    field_simp
  simp_rw [hsc]
  exact hint0

end MathlibExt.Probability.Statistics.MLEAsymptoticNormality
