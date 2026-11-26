/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Expected truncated lifetime as a survival integral

For a measurable, almost surely nonnegative lifetime, the mean of the lifetime capped at a
finite nonnegative horizon is the integral of the survival function up to that horizon. The
uncapped formula uses the extended nonnegative integral and does not assume a finite mean.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

private theorem integral_min_eq_integral_survival {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {L : Ω → ℝ} (hL : Measurable L)
    (hnonneg : 0 ≤ᵐ[μ] L) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, min (L ω) T ∂μ) = ∫ t in (0 : ℝ)..T, μ.real {ω | t < L ω} := by
  have hcap : 0 ≤ᵐ[μ] (fun ω => min (L ω) T) :=
    hnonneg.mono fun _ hω => le_min hω hT
  have hi : Integrable (fun ω => min (L ω) T) μ := by
    refine (integrable_const T).mono' (hL.min measurable_const).aestronglyMeasurable ?_
    filter_upwards [hcap] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω]
    exact min_le_right _ _
  rw [hi.integral_eq_integral_meas_lt hcap, intervalIntegral.integral_of_le hT]
  have hzero : ∀ᵐ t : ℝ, t ∈ Ioi (0 : ℝ) \ Ioc 0 T →
      μ.real {ω | t < min (L ω) T} = 0 := by
    refine Filter.Eventually.of_forall fun t ht => ?_
    have htT : ¬ t < T := fun hlt => ht.2 ⟨ht.1, hlt.le⟩
    simp [lt_min_iff, htT]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Ioi Ioc_subset_Ioi_self hzero]
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [(volume : Measure ℝ).ae_ne T] with t hne ht
  have htT : t < T := lt_of_le_of_ne ht.2 hne
  simp [lt_min_iff, htT]

/-- **Expected truncated lifetime as a survival integral.** Let `L` be a measurable,
almost surely nonnegative lifetime under a probability measure `μ`. For every finite horizon
`T ≥ 0`, the mean of `min L T` is `∫ t in 0..T, μ.real {ω | t < L ω}`. The uncapped mean,
taken as an extended nonnegative integral, is `∫⁻ t in Set.Ioi 0, μ {ω | t < L ω}` and can
be infinite. Neither result requires a density or an atomless lifetime law.
The uncapped formula appears in Grinstead and Snell, *Introduction to Probability*,
§6.3, Exercise 13. -/
theorem truncatedLifetime_survival_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L : Ω → ℝ} (hL : Measurable L)
    (hnonneg : 0 ≤ᵐ[μ] L) :
    (∀ T : ℝ, 0 ≤ T → (∫ ω, min (L ω) T ∂μ) = ∫ t in (0 : ℝ)..T, μ.real {ω | t < L ω}) ∧
      (∫⁻ ω, ENNReal.ofReal (L ω) ∂μ) = ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < L ω} := by
  exact ⟨fun _ hT => integral_min_eq_integral_survival μ hL hnonneg hT,
    lintegral_eq_lintegral_meas_lt μ hnonneg hL.aemeasurable⟩

end ProbabilityTheory
