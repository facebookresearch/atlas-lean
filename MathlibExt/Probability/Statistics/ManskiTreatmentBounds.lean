/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Linarith

@[expose] public section

namespace WantedExt.Probability.Statistics.ManskiTreatmentBoundsWanted

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lower no-assumption bound.** The lower bound `E[Y₁ 1_T] - (E[Y₀ 1_{Tᶜ}] + P(T))` on the
average treatment effect. -/
noncomputable def lowerBound (μ : Measure Ω) (T : Set Ω) (Y₀ Y₁ : Ω → ℝ) : ℝ :=
  (∫ ω in T, Y₁ ω ∂μ) - ((∫ ω in Tᶜ, Y₀ ω ∂μ) + μ.real T)

/-- **Upper no-assumption bound.** The upper bound `E[Y₁ 1_T] + P(Tᶜ) - E[Y₀ 1_{Tᶜ}]` on the
average treatment effect. -/
noncomputable def upperBound (μ : Measure Ω) (T : Set Ω) (Y₀ Y₁ : Ω → ℝ) : ℝ :=
  ((∫ ω in T, Y₁ ω ∂μ) + μ.real Tᶜ) - ∫ ω in Tᶜ, Y₀ ω ∂μ

/-- **Soundness, width and sign of the no-assumption bounds.** Let `μ` be a
probability measure on `Ω`, `T` a measurable event (treatment), and `Y₀, Y₁ : Ω → ℝ` measurable
potential outcomes with values in `[0, 1]`. Then the average treatment effect
`∫ Y₁ dμ - ∫ Y₀ dμ` lies between `lowerBound` and `upperBound`, the width
`upperBound - lowerBound` equals `1`, and `lowerBound ≤ 0 ≤ upperBound`.

Sources: C. F. Manski, "Nonparametric bounds on treatment effects", Am. Econ. Rev. 80(2) (1990)
319–323. -/
theorem bounds_sound (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Set Ω)
    (hT : MeasurableSet T) (Y₀ Y₁ : Ω → ℝ) (h₀ : Measurable Y₀) (h₁ : Measurable Y₁)
    (h₀01 : ∀ ω, 0 ≤ Y₀ ω ∧ Y₀ ω ≤ 1) (h₁01 : ∀ ω, 0 ≤ Y₁ ω ∧ Y₁ ω ≤ 1) :
    lowerBound μ T Y₀ Y₁ ≤ (∫ ω, Y₁ ω ∂μ) - ∫ ω, Y₀ ω ∂μ ∧
      (∫ ω, Y₁ ω ∂μ) - ∫ ω, Y₀ ω ∂μ ≤ upperBound μ T Y₀ Y₁ ∧
      upperBound μ T Y₀ Y₁ - lowerBound μ T Y₀ Y₁ = 1 ∧
      lowerBound μ T Y₀ Y₁ ≤ 0 ∧ 0 ≤ upperBound μ T Y₀ Y₁ := by
  have integrable {Y : Ω → ℝ} (hY : Measurable Y) (hY01 : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) :
      Integrable Y μ :=
    Integrable.of_bound hY.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hY01 ω).1]
        exact (hY01 ω).2)
  have setIntegral_bounds {Y : Ω → ℝ} (hY : Integrable Y μ)
      (hY01 : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) (s : Set Ω) :
      0 ≤ (∫ ω in s, Y ω ∂μ) ∧ (∫ ω in s, Y ω ∂μ) ≤ μ.real s := by
    refine ⟨integral_nonneg (fun ω => (hY01 ω).1), ?_⟩
    calc
      (∫ ω in s, Y ω ∂μ) ≤ ∫ _ in s, (1 : ℝ) ∂μ :=
        integral_mono hY.integrableOn (integrable_const 1) (fun ω => (hY01 ω).2)
      _ = μ.real s := by simp
  have hY₀ := integrable h₀ h₀01
  have hY₁ := integrable h₁ h₁01
  obtain ⟨h₀T_nonneg, h₀T_le⟩ := setIntegral_bounds hY₀ h₀01 T
  obtain ⟨h₀Tc_nonneg, h₀Tc_le⟩ := setIntegral_bounds hY₀ h₀01 Tᶜ
  obtain ⟨h₁T_nonneg, h₁T_le⟩ := setIntegral_bounds hY₁ h₁01 T
  obtain ⟨h₁Tc_nonneg, h₁Tc_le⟩ := setIntegral_bounds hY₁ h₁01 Tᶜ
  have hmass : μ.real T + μ.real Tᶜ = 1 := by
    simpa only [probReal_univ] using measureReal_add_measureReal_compl (μ := μ) hT
  simp only [lowerBound, upperBound, ← integral_add_compl hT hY₀, ← integral_add_compl hT hY₁]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h₀T_le, h₁Tc_nonneg]
  · linarith only [h₀T_nonneg, h₁Tc_le]
  · linarith only [hmass]
  · linarith only [h₀Tc_nonneg, h₁T_le]
  · linarith only [h₀Tc_le, h₁T_nonneg]

/-- **Sharpness of the no-assumption bounds.** Let `μ` be a probability measure on
`Ω`, `T` a measurable event, and `Y₀, Y₁ : Ω → ℝ` measurable with values in `[0, 1]`. Then there
are measurable potential outcomes `Y₀', Y₁'` with values in `[0, 1]` that agree with the observed
ones (`Y₁' = Y₁` on `T` and `Y₀' = Y₀` on `Tᶜ`) and whose average treatment effect equals
`lowerBound μ T Y₀ Y₁`, and likewise a pair whose average treatment effect equals
`upperBound μ T Y₀ Y₁`.

Sources: C. F. Manski, "Nonparametric bounds on treatment effects", Am. Econ. Rev. 80(2) (1990)
319–323. -/
theorem bounds_sharp (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Set Ω)
    (hT : MeasurableSet T) (Y₀ Y₁ : Ω → ℝ) (h₀ : Measurable Y₀) (h₁ : Measurable Y₁)
    (h₀01 : ∀ ω, 0 ≤ Y₀ ω ∧ Y₀ ω ≤ 1) (h₁01 : ∀ ω, 0 ≤ Y₁ ω ∧ Y₁ ω ≤ 1) :
    (∃ Y₀' Y₁' : Ω → ℝ, Measurable Y₀' ∧ Measurable Y₁' ∧
        (∀ ω, 0 ≤ Y₀' ω ∧ Y₀' ω ≤ 1) ∧ (∀ ω, 0 ≤ Y₁' ω ∧ Y₁' ω ≤ 1) ∧
        (∀ ω ∈ T, Y₁' ω = Y₁ ω) ∧ (∀ ω ∈ Tᶜ, Y₀' ω = Y₀ ω) ∧
        (∫ ω, Y₁' ω ∂μ) - ∫ ω, Y₀' ω ∂μ = lowerBound μ T Y₀ Y₁) ∧
      ∃ Y₀' Y₁' : Ω → ℝ, Measurable Y₀' ∧ Measurable Y₁' ∧
        (∀ ω, 0 ≤ Y₀' ω ∧ Y₀' ω ≤ 1) ∧ (∀ ω, 0 ≤ Y₁' ω ∧ Y₁' ω ≤ 1) ∧
        (∀ ω ∈ T, Y₁' ω = Y₁ ω) ∧ (∀ ω ∈ Tᶜ, Y₀' ω = Y₀ ω) ∧
        (∫ ω, Y₁' ω ∂μ) - ∫ ω, Y₀' ω ∂μ = upperBound μ T Y₀ Y₁ := by
  classical
  have complete {s : Set Ω} (hs : MeasurableSet s) {Y : Ω → ℝ} (hY : Measurable Y)
      (hY01 : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) (c : ℝ) (hc : 0 ≤ c ∧ c ≤ 1) :
      ∃ Y' : Ω → ℝ, Measurable Y' ∧ (∀ ω, 0 ≤ Y' ω ∧ Y' ω ≤ 1) ∧
        (∀ ω ∈ s, Y' ω = Y ω) ∧
        (∫ ω, Y' ω ∂μ) = (∫ ω in s, Y ω ∂μ) + μ.real sᶜ * c := by
    let Y' : Ω → ℝ := s.piecewise Y (fun _ => c)
    have hm : Measurable Y' := hY.piecewise hs measurable_const
    have hobs : Set.EqOn Y' Y s := fun ω hω => by simp [Y', hω]
    have hmiss : Set.EqOn Y' (fun _ => c) sᶜ := fun ω hω => by
      have hω' : ω ∉ s := hω
      simp [Y', hω']
    have h01 (ω : Ω) : 0 ≤ Y' ω ∧ Y' ω ≤ 1 := by
      by_cases hω : ω ∈ s
      · rw [hobs hω]
        exact hY01 ω
      · rw [hmiss hω]
        exact hc
    have hi : Integrable Y' μ :=
      Integrable.of_bound hm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (h01 ω).1]
          exact (h01 ω).2)
    refine ⟨Y', hm, h01, fun _ hω => hobs hω, ?_⟩
    rw [← integral_add_compl hs hi, setIntegral_congr_fun hs hobs,
      setIntegral_congr_fun hs.compl hmiss, integral_const, smul_eq_mul,
      measureReal_restrict_apply_univ]
  constructor
  · obtain ⟨Y₀', hm₀, hb₀, ho₀, hi₀⟩ := complete hT.compl h₀ h₀01 1 (by simp)
    obtain ⟨Y₁', hm₁, hb₁, ho₁, hi₁⟩ := complete hT h₁ h₁01 0 (by simp)
    refine ⟨Y₀', Y₁', hm₀, hm₁, hb₀, hb₁, ho₁, ho₀, ?_⟩
    simp [hi₀, hi₁, lowerBound]
  · obtain ⟨Y₀', hm₀, hb₀, ho₀, hi₀⟩ := complete hT.compl h₀ h₀01 0 (by simp)
    obtain ⟨Y₁', hm₁, hb₁, ho₁, hi₁⟩ := complete hT h₁ h₁01 1 (by simp)
    refine ⟨Y₀', Y₁', hm₀, hm₁, hb₀, hb₁, ho₁, ho₀, ?_⟩
    simp [hi₀, hi₁, upperBound]

end WantedExt.Probability.Statistics.ManskiTreatmentBoundsWanted
