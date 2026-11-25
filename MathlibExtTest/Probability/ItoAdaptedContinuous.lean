/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.ItoAdaptedContinuous
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} [F.IsComplete P]

-- A genuinely smaller sigma algebra needs completeness, not just an ambient measure.
example {X Y : ℝ≥0 → Ω → ℝ} (hX : Adapted F X)
    (h : ∀ t, X t =ᵐ[P] Y t) : Adapted F Y :=
  hX.congr_ae_of_complete h

example {B H : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (hH : IsProgressive F H)
    (hH2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Ioc (0 : ℝ) t,
      ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    ∃ J : ℝ≥0 → Ω → ℝ, IsProgressive F J ∧ (∀ ω, Continuous (fun t ↦ J t ω)) ∧
      (∀ t, MemLp (J t) 2 P) ∧ ∀ t, J t =ᵐ[P] itoIntegral P F B H t := by
  obtain ⟨J, hJ, hp, hc, he⟩ := itoIntegral_exists_continuous_martingale hB hBF hInd hH hH2
  exact ⟨J, hp, hc, fun t ↦ (memLp_itoIntegral P F B H t).ae_eq (he t).symm, he⟩
end

-- Continuity only almost surely suffices for uniqueness of versions; no filtration is needed.
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : ℝ → Ω → ℝ}
    (hX : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t ↦ Y t ω)) (he : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y :=
  indistinguishable_of_ae_eq_of_continuous hX hY he

-- Nonzero deterministic integrands identify the version with the actual Brownian increment.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P) :
    ∃ J : ℝ≥0 → Ω → ℝ, Martingale J F P ∧ (∀ ω, Continuous fun t ↦ J t ω) ∧
      J ≡ᵐ[P] (fun t ω ↦ 2 * (B t ω - B 0 ω)) := by
  have := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have h2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Ioc (0 : ℝ) t,
      ‖(2 : ℝ)‖ₑ ^ 2) ∂P ≠ ∞ := by
    intro t
    simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
    finiteness
  obtain ⟨J, hm, _, hc, he⟩ := itoIntegral_exists_continuous_martingale
    hB hBF hInd (isProgressive_const F (2 : ℝ)) h2
  refine ⟨J, hm, hc, indistinguishable_of_ae_eq_of_continuous
    (Filter.Eventually.of_forall hc) ?_ ?_⟩
  · filter_upwards [hB.cont] with ω hω
    exact continuous_const.mul (hω.sub continuous_const)
  · intro t
    refine (he t).trans ?_
    have hi := itoIntegral_deterministic_eq hB hBF hInd
      (show ContDiff ℝ 1 (fun _ : ℝ ↦ (2 : ℝ)) from contDiff_const) t
    simpa only [deriv_const, zero_mul, intervalIntegral.integral_zero, sub_zero, mul_sub]
      using hi

-- At zero integrand, the whole version is zero on one common full-measure set.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} [F.IsComplete P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P) :
    ∃ J : ℝ≥0 → Ω → ℝ, Martingale J F P ∧
      (∀ ω, Continuous fun t ↦ J t ω) ∧ J ≡ᵐ[P] (fun _ _ ↦ 0) := by
  obtain ⟨J, hm, _, hc, he⟩ := itoIntegral_exists_continuous_martingale
    hB hBF hInd (isProgressive_const F (0 : ℝ)) (by simp)
  refine ⟨J, hm, hc, indistinguishable_of_ae_eq_of_continuous
    (Filter.Eventually.of_forall hc) (Filter.Eventually.of_forall fun _ ↦ continuous_const) ?_⟩
  intro t
  refine (he t).trans ?_
  simpa using itoIntegral_deterministic_eq hB hBF hInd
    (show ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) from contDiff_const) t

section NullAtom
local instance : MeasurableSpace Bool := ⊤

-- The ambient finite space is complete, but its trivial filtration is not.
example : (Measure.dirac false).IsComplete := ⟨fun _ _ ↦ trivial⟩

example : (fun _ : Bool ↦ (0 : ℝ)) =ᵐ[Measure.dirac false]
    (fun ω ↦ if ω then (1 : ℝ) else 0) := by simp [Filter.EventuallyEq]

example : ¬ Adapted (⊥ : Filtration ℝ≥0 (⊤ : MeasurableSpace Bool))
    (fun _ ω ↦ if ω then (1 : ℝ) else 0) := by
  intro h
  obtain ⟨c, hc⟩ := eq_const_of_measurable_bot (h 0)
  have h0 := congr_fun hc false
  have h1 := congr_fun hc true
  simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
  linarith
end NullAtom
