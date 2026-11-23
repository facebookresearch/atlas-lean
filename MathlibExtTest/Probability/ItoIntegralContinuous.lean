/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoIntegralContinuous
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import MathlibExtTest.Probability.ItoIntegralSampleDependent

/-!
# Tests for the continuous modification of the Itô integral

These probes exercise one returned process simultaneously at time zero, two nested compact
horizons, and a later time. The continuity field is applied to an arbitrary sample, including
samples outside every full-measure set used in the construction. A sample-dependent probe uses the
sign selected by `B 1` on `(1, 2]` and its negative on `(2, 3]`, and checks continuity at all three
window boundaries.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExtTest.Probability.ItoIntegralContinuous

open MathlibExtTest.Probability.ItoIntegralSampleDependent

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P) :
    ∃ J : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t ↦ J t ω) ∧
      J 0 =ᵐ[P] itoIntegral P F B (fun _ _ ↦ 1) 0 ∧
      J 1 =ᵐ[P] itoIntegral P F B (fun _ _ ↦ 1) 1 ∧
      J 2 =ᵐ[P] itoIntegral P F B (fun _ _ ↦ 1) 2 ∧
      J 3 =ᵐ[P] itoIntegral P F B (fun _ _ ↦ 1) 3 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hH : IsProgressive F (fun _ _ ↦ (1 : ℝ)) := isProgressive_const F 1
  have hH2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖(fun _ _ ↦ (1 : ℝ)) u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞ := by
    intro t
    simp [Real.volume_Ioc]
  obtain ⟨J, hc, he⟩ :=
    itoIntegral_continuous_modification
      hB hBF hInd hH hH2
  exact ⟨J, hc, he 0, he 1, he 2, he 3⟩

example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hH2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) (ω : Ω) :
    ∃ J : ℝ≥0 → Ω → ℝ, Continuous (fun t ↦ J t ω) ∧
      ∀ t, J t =ᵐ[P] itoIntegral P F B H t := by
  obtain ⟨J, hc, he⟩ :=
    itoIntegral_continuous_modification
      hB hBF hInd hH hH2
  exact ⟨J, hc ω, he⟩

/-- The sample-dependent adjacent-window integrand has a modification continuous at its
three window boundaries for every sample. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P) (ω : Ω) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      (∀ ω', Continuous fun t ↦ J t ω') ∧
      ContinuousAt (fun t ↦ J t ω) 1 ∧
      ContinuousAt (fun t ↦ J t ω) 2 ∧
      ContinuousAt (fun t ↦ J t ω) 3 ∧
      ∀ t, J t =ᵐ[P] itoIntegral P F B
        (signedWindow B 1 2 - signedWindow B 2 3) t := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have h12 := signedWindow_progressive hBF 1 2 (by norm_num)
  have h23 := signedWindow_progressive hBF 2 3 (by norm_num)
  have hH : IsProgressive F (signedWindow B 1 2 - signedWindow B 2 3) := h12.sub h23
  have hH2 := fun t ↦ signedDifference_energy_ne_top (P := P) hBF t
  obtain ⟨J, hJc, hJeq⟩ := itoIntegral_continuous_modification hB hBF hInd hH hH2
  exact ⟨J, hJc, (hJc ω).continuousAt, (hJc ω).continuousAt,
    (hJc ω).continuousAt, hJeq⟩

#print axioms itoIntegral_continuous_modification

end MathlibExtTest.Probability.ItoIntegralContinuous
