/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Real

/-!
# Diagnostic joint law and predictive values

For a disease event `D` and a positive-test event `T` in a probability
space, the four joint masses determined by prevalence `π`, sensitivity
`se` and specificity `sp` determine the test-positive and test-negative
masses and the predictive values as real ratios. Raising prevalence at
fixed sensitivity and specificity raises the positive predictive value.

This is a statement about the declared joint law only. It contains no
screening, diagnosis, treatment or threshold recommendation and no
empirical sensitivity or specificity claim.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.Probability.Statistics.DiagnosticObservation

/-- **Diagnostic law and prevalence transport.** In a probability space
with disease event `D` and positive-test event `T`, if the prevalence is
`π`, the sensitivity is `se` and the specificity is `sp` in the sense
that the four joint masses are `π * se`, `π * (1 - se)`,
`(1 - π) * (1 - sp)` and `(1 - π) * sp`, then the test-positive mass is
`π * se + (1 - π) * (1 - sp)`, the test-negative mass is
`(1 - π) * sp + π * (1 - se)`, and (as real ratios) the predictive
values are `π * se / (π * se + (1 - π) * (1 - sp))` and
`(1 - π) * sp / ((1 - π) * sp + π * (1 - se))`. -/
theorem diagnostic_predictive_values {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {D T : Set Ω} {π se sp : ℝ}
    (hD : MeasurableSet D) (hT : MeasurableSet T)
    (hTP : μ.real (D ∩ T) = π * se) (hFN : μ.real (D ∩ Tᶜ) = π * (1 - se))
    (hFP : μ.real (Dᶜ ∩ T) = (1 - π) * (1 - sp))
    (hTN : μ.real (Dᶜ ∩ Tᶜ) = (1 - π) * sp) :
    μ.real T = π * se + (1 - π) * (1 - sp) ∧
    μ.real Tᶜ = (1 - π) * sp + π * (1 - se) ∧
    μ.real (D ∩ T) / μ.real T = π * se / (π * se + (1 - π) * (1 - sp)) ∧
    μ.real (Dᶜ ∩ Tᶜ) / μ.real Tᶜ = (1 - π) * sp / ((1 - π) * sp + π * (1 - se)) := by
  have hDc : MeasurableSet Dᶜ := hD.compl
  have hTc : MeasurableSet Tᶜ := hT.compl
  have hDcT : MeasurableSet (Dᶜ ∩ T) := hDc.inter hT
  have hDTc : MeasurableSet (D ∩ Tᶜ) := hD.inter hTc
  have hdisjT : Disjoint (D ∩ T) (Dᶜ ∩ T) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxD, _⟩ ⟨hxDc, _⟩
    exact hxDc hxD
  have hunionT : (D ∩ T) ∪ (Dᶜ ∩ T) = T := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro (⟨_, hxT⟩ | ⟨_, hxT⟩) <;> exact hxT
    · intro hxT
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨hxD, hxT⟩
      · exact Or.inr ⟨hxD, hxT⟩
  have hdisjTc : Disjoint (Dᶜ ∩ Tᶜ) (D ∩ Tᶜ) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxDc, _⟩ ⟨hxD, _⟩
    exact hxDc hxD
  have hunionTc : (Dᶜ ∩ Tᶜ) ∪ (D ∩ Tᶜ) = Tᶜ := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro (⟨_, hxTc⟩ | ⟨_, hxTc⟩) <;> exact hxTc
    · intro hxTc
      by_cases hxD : x ∈ D
      · exact Or.inr ⟨hxD, hxTc⟩
      · exact Or.inl ⟨hxD, hxTc⟩
  have hTmass : μ.real T = π * se + (1 - π) * (1 - sp) := by
    have h := measureReal_union hdisjT hDcT (measure_ne_top μ _) (measure_ne_top μ _)
    rw [hunionT, hTP, hFP] at h
    exact h
  have hTcmass : μ.real Tᶜ = (1 - π) * sp + π * (1 - se) := by
    have h := measureReal_union hdisjTc hDTc (measure_ne_top μ _) (measure_ne_top μ _)
    rw [hunionTc, hTN, hFN] at h
    exact h
  refine ⟨hTmass, hTcmass, ?_, ?_⟩
  · rw [hTP, hTmass]
  · rw [hTN, hTcmass]

/-- Prevalence transport example: at sensitivity and specificity `3/4`,
raising prevalence from `1/10` to `1/2` raises the positive predictive
value from `1/4` to `3/4`. -/
theorem diagnostic_ppv_prevalence_example :
    ((1 / 10 : ℝ) * (3 / 4) / ((1 / 10 : ℝ) * (3 / 4) + (1 - 1 / 10) * (1 - 3 / 4)) = 1 / 4) ∧
    ((1 / 2 : ℝ) * (3 / 4) / ((1 / 2 : ℝ) * (3 / 4) + (1 - 1 / 2) * (1 - 3 / 4)) = 3 / 4) := by
  constructor <;> norm_num

end MathlibExt.Probability.Statistics.DiagnosticObservation
