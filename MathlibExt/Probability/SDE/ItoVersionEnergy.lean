/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.ItoAdaptedContinuous

/-!
# Integrated energy of Itô versions

Tonelli's theorem and the actual Itô isometry give finite integrated second
moments for any jointly measurable version on a finite horizon. Under a complete
filtration, the existing continuous adapted martingale version therefore remains
in the progressive finite-energy class required by the classical Picard argument.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- A jointly measurable version of the actual Itô integral has integrated
energy at most the horizon times the input energy. Neither completeness nor
path continuity is needed for this estimate; version equality is only required
on the horizon in question. -/
theorem integrandDist_itoIntegral_version_zero_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H J : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hJ : Measurable fun p : ℝ × Ω ↦ J p.1.toNNReal p.2) (T : ℝ≥0)
    (he : ∀ t ≤ T, J t =ᵐ[P] itoIntegral P F B H t)
    (hH2 : integrandDist P H (fun _ _ ↦ 0) T ≠ ∞) :
    integrandDist P J (fun _ _ ↦ 0) T ≤
      (T : ℝ≥0∞) * integrandDist P H (fun _ _ ↦ 0) T := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hmono {s : ℝ≥0} (hs : s ≤ T) :
      integrandDist P H (fun _ _ ↦ 0) s ≤ integrandDist P H (fun _ _ ↦ 0) T :=
    lintegral_mono fun _ ↦ lintegral_mono_set
      (Ioc_subset_Ioc_right (by exact_mod_cast hs))
  have hm : Measurable fun p : Ω × ℝ ↦ ‖J p.2.toNNReal p.1‖ₑ^2 :=
    (hJ.comp measurable_swap).eNorm.pow_const 2
  simp only [integrandDist, sub_zero]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ _s in Ioc (0 : ℝ) T, integrandDist P H (fun _ _ ↦ 0) T := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro s hs
      have ht : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
      have hfinite : ∫⁻ ω, (∫⁻ u in Ioc (0 : ℝ) s.toNNReal,
          ‖H u.toNNReal ω‖ₑ^2) ∂P ≠ ∞ := by
        simpa only [integrandDist, sub_zero] using ne_top_of_le_ne_top hH2 (hmono ht)
      calc
        _ = ∫⁻ ω, ‖itoIntegral P F B H s.toNNReal ω‖ₑ^2 ∂P :=
          lintegral_congr_ae ((he s.toNNReal ht).fun_comp (fun x ↦ ‖x‖ₑ^2))
        _ = integrandDist P H (fun _ _ ↦ 0) s.toNNReal := by
          simpa only [integrandDist, sub_zero] using
            lintegral_itoIntegral_sq_of_isProgressive hB hBF hInd hH s.toNNReal hfinite
        _ ≤ _ := hmono ht
    _ = _ := by simp [mul_comm, integrandDist]


/-- For a complete filtration, a progressive locally finite-energy input has a
continuous progressive martingale Itô version with locally finite integrated
second moments and the explicit horizon-times-input-energy bound. -/
theorem itoIntegral_exists_continuous_martingale_finite_energy
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hH2 : ∀ T, integrandDist P H (fun _ _ ↦ 0) T ≠ ∞) :
    ∃ J : ℝ≥0 → Ω → ℝ, Martingale J F P ∧ IsProgressive F J ∧
      (∀ ω, Continuous fun t ↦ J t ω) ∧
      (∀ t, J t =ᵐ[P] itoIntegral P F B H t) ∧
      (∀ T, integrandDist P J (fun _ _ ↦ 0) T ≠ ∞) ∧
      ∀ T, integrandDist P J (fun _ _ ↦ 0) T ≤
        (T : ℝ≥0∞) * integrandDist P H (fun _ _ ↦ 0) T := by
  have hfinite : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Ioc (0 : ℝ) t,
      ‖H u.toNNReal ω‖ₑ^2) ∂P ≠ ∞ := by
    simpa only [integrandDist, sub_zero] using hH2
  obtain ⟨J, hm, hp, hc, he⟩ :=
    itoIntegral_exists_continuous_martingale hB hBF hInd hH hfinite
  have hb (T : ℝ≥0) := integrandDist_itoIntegral_version_zero_le
    hB.toIsPreBrownianReal hBF hInd hH (IsProgressive.measurable_toNNReal hp) T
    (fun t _ ↦ he t) (hH2 T)
  exact ⟨J, hm, hp, hc, he,
    fun T ↦ ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (hH2 T)) (hb T), hb⟩

end ProbabilityTheory
