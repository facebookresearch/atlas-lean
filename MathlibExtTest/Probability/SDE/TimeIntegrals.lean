/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.SDE.TimeIntegrals

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H) :
    Adapted F (fun t ω ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal ω) :=
  IsProgressive.adapted_timeIntegral hH

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hc : ∀ ω, Continuous (H · ω)) :
    IsProgressive F (fun t ω ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal ω) :=
  IsProgressive.timeIntegral hH hc

example {Ω : Type*} [MeasurableSpace Ω] (t : ℝ≥0) :
    (∫ _s in (0 : ℝ)..t, (3 : ℝ)) = 3 * t := by
  simp [intervalIntegral.integral_const, mul_comm]

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℝ≥0 → Ω → ℝ) :
    ∫⁻ ω, ‖∫ s in (0 : ℝ)..0, H s.toNNReal ω‖ₑ^2 ∂P = 0 := by simp

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {H : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous (H · ω)) (t : ℝ≥0) :
    ∫⁻ ω, ‖∫ s in (0 : ℝ)..t, H s.toNNReal ω‖ₑ^2 ∂P ≤
      (t : ℝ≥0∞) * integrandDist P H (fun _ _ ↦ 0) t :=
  lintegral_timeIntegral_sq_le P hc t

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hc : ∀ ω, Continuous (H · ω)) (T : ℝ≥0)
    (hE : integrandDist P H (fun _ _ ↦ 0) T ≠ ∞) :
    MemLp (fun ω ↦ ∫ s in (0 : ℝ)..T, H s.toNNReal ω) 2 P :=
  memLp_timeIntegral hH hc T hE

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {H : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous (H · ω)) (T : ℝ≥0)
    (hE : integrandDist P H (fun _ _ ↦ 0) T ≠ ∞) :
    integrandDist P (fun t ω ↦ ∫ s in (0 : ℝ)..t, H s.toNNReal ω) (fun _ _ ↦ 0) T ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hE)
    (integrandDist_timeIntegral_zero_le P hc T)

example (T : ℝ≥0) :
    Continuous (fun t : ℝ≥0 ↦ ∫ s in (0 : ℝ)..t, |(s.toNNReal : ℝ) - T|) :=
  continuous_timeIntegral (H := fun s : ℝ≥0 ↦ |(s : ℝ) - T|) (by fun_prop)

example : (⨆ (t : ℝ≥0) (_ : t ≤ 2), ‖∫ _s in (0 : ℝ)..t, (-3 : ℝ)‖ₑ^2) = 36 := by
  apply le_antisymm
  · have h := iSup_enorm_timeIntegral_sq_le (H := fun _ ↦ (-3 : ℝ)) continuous_const 2
    norm_num [Real.eNorm_eq_ofReal_abs, Real.volume_Ioc] at h ⊢
    exact h
  · calc
      (36 : ℝ≥0∞) = ‖∫ _s in (0 : ℝ)..(2 : ℝ≥0), (-3 : ℝ)‖ₑ^2 := by
        norm_num [Real.eNorm_eq_ofReal_abs]
      _ ≤ _ := by
        apply le_iSup_of_le (2 : ℝ≥0)
        simp

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ _ω : Ω, ‖∫ _s in (0 : ℝ)..(2 : ℝ≥0), (3 : ℝ)‖ₑ^2 ∂P =
      (2 : ℝ≥0∞) * integrandDist P (fun _ _ ↦ (3 : ℝ)) (fun _ _ ↦ 0) 2 := by
  norm_num [integrandDist, Real.eNorm_eq_ofReal_abs, Real.volume_Ioc]

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {H : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous (H · ω)) (T : ℝ≥0) :
    ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : t ≤ T),
      ‖∫ s in (0 : ℝ)..t, H s.toNNReal ω‖ₑ^2) ∂P ≤
        (T : ℝ≥0∞) * integrandDist P H (fun _ _ ↦ 0) T :=
  lintegral_iSup_timeIntegral_sq_le P hc T


example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X Y : ℝ≥0 → Ω → ℝ} (hX : ∀ ω, Continuous (X · ω))
    (hY : ∀ ω, Continuous (Y · ω)) (t : ℝ≥0) :
    ∫⁻ ω, ‖(∫ s in (0 : ℝ)..t, X s.toNNReal ω) -
      (∫ s in (0 : ℝ)..t, Y s.toNNReal ω)‖ₑ^2 ∂P ≤
        (t : ℝ≥0∞) * integrandDist P X Y t :=
  lintegral_timeIntegral_sub_sq_le P hX hY t
