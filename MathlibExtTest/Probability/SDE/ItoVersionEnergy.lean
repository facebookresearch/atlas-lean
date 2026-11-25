/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.SDE.ItoVersionEnergy

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H J : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hJ : Measurable fun p : ℝ × Ω ↦ J p.1.toNNReal p.2) (T : ℝ≥0)
    (he : ∀ t ≤ T, J t =ᵐ[P] itoIntegral P F B H t)
    (hH2 : integrandDist P H (fun _ _ ↦ 0) T ≠ ∞) :
    integrandDist P J (fun _ _ ↦ 0) T ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hH2)
    (integrandDist_itoIntegral_version_zero_le hB hBF hInd hH hJ T he hH2)

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hH2 : ∀ T, integrandDist P H (fun _ _ ↦ 0) T ≠ ∞) :
    ∃ J : ℝ≥0 → Ω → ℝ, IsProgressive F J ∧
      (∀ ω, Continuous fun t ↦ J t ω) ∧
      (∀ t, J t =ᵐ[P] itoIntegral P F B H t) ∧
      ∀ T, integrandDist P J (fun _ _ ↦ 0) T ≠ ∞ := by
  obtain ⟨J, _hm, hp, hc, he, hfinite, _hbound⟩ :=
    itoIntegral_exists_continuous_martingale_finite_energy hB hBF hInd hH hH2
  exact ⟨J, hp, hc, he, hfinite⟩

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (J : ℝ≥0 → Ω → ℝ) :
    integrandDist P J (fun _ _ ↦ 0) 0 = 0 := by simp [integrandDist]

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {J : ℝ≥0 → Ω → ℝ}
    (hJ : Measurable fun p : ℝ × Ω ↦ J p.1.toNNReal p.2) (T : ℝ≥0)
    (he : ∀ t ≤ T, J t =ᵐ[P] itoIntegral P F B (fun _ _ ↦ 0) t) :
    integrandDist P J (fun _ _ ↦ 0) T = 0 := by
  have h := integrandDist_itoIntegral_version_zero_le hB hBF hInd
    (isProgressive_const F (0 : ℝ)) hJ T he (by simp [integrandDist])
  have hz : integrandDist P (fun _ _ ↦ 0) (fun _ _ ↦ 0) T = 0 := by
    simp [integrandDist]
  simpa only [hz, mul_zero, nonpos_iff_eq_zero] using h

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P) :
    ∃ J : ℝ≥0 → Ω → ℝ, Martingale J F P ∧
      J ≡ᵐ[P] (fun t ω ↦ -3 * (B t ω - B 0 ω)) ∧
      integrandDist P J (fun _ _ ↦ 0) 2 ≤ 36 := by
  have := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hH2 : ∀ T : ℝ≥0, integrandDist P (fun _ _ ↦ (-3 : ℝ)) (fun _ _ ↦ 0) T ≠ ∞ := by
    intro T
    simp only [integrandDist, sub_zero, lintegral_const, Measure.restrict_apply_univ,
      Real.volume_Ioc]
    finiteness
  obtain ⟨J, hm, _hp, hc, he, _hf, hb⟩ :=
    itoIntegral_exists_continuous_martingale_finite_energy hB hBF hInd
      (isProgressive_const F (-3 : ℝ)) hH2
  refine ⟨J, hm, ?_, ?_⟩
  · apply indistinguishable_of_ae_eq_of_continuous (Filter.Eventually.of_forall hc)
    · filter_upwards [hB.cont] with ω hω
      exact continuous_const.mul (hω.sub continuous_const)
    · intro t
      refine (he t).trans ?_
      have hi := itoIntegral_deterministic_eq hB hBF hInd
        (show ContDiff ℝ 1 (fun _ : ℝ ↦ (-3 : ℝ)) from contDiff_const) t
      simpa only [deriv_const, zero_mul, intervalIntegral.integral_zero, sub_zero, mul_sub]
        using hi
  · have hb2 := hb 2
    norm_num [integrandDist, Real.eNorm_eq_ofReal_abs, Real.volume_Ioc] at hb2 ⊢
    exact hb2
