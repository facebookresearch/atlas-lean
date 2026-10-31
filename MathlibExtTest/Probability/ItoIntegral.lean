/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoIntegral

/-!
# Tests for the Itô integral

Non-vacuity of `IsItoApproximable` (elementary integrands), the value on `1_{(1, 2]}`, the
constant integrand (`∫_0^t 1 dB = B t - B 0`), the Ornstein–Uhlenbeck identification at `θ = 0`,
the isometry and martingale property instantiated on an elementary integrand, and the junk value
`0` of `itoIntegralL2` on integrands that are not Itô-approximable.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.ItoIntegral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- `1_{(1, 2]}` as an elementary integrand. -/
noncomputable def one12 (F : Filtration ℝ≥0 mΩ) : ElementaryIntegrand F :=
  ElementaryIntegrand.single 1 2 (by norm_num) (fun _ ↦ (1 : ℝ)) measurable_const 1 (by simp)

/-- Elementary integrands are Itô-approximable: `IsItoApproximable` is not vacuous. -/
example (t : ℝ≥0) : IsItoApproximable P F (one12 F).toProcess t :=
  isItoApproximable_toProcess P _ t

/-- The Itô integral of `1_{(1, 2]}` up to time `3` is `B 2 - B 1`. -/
example (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) :
    itoIntegral P F B (fun u _ ↦ Set.indicator (Set.Ioc 1 2) (fun _ ↦ (1 : ℝ)) u) 3 =ᵐ[P]
      fun ω ↦ B 2 ω - B 1 ω := by
  filter_upwards [itoIntegral_indicator_Ioc hB hBF hInd (a := 1) (b := 2) (by norm_num)
    (ξ := fun _ ↦ (1 : ℝ)) measurable_const 1 (by simp) 3] with ω hω
  rw [hω, min_eq_left (by rw [← NNReal.coe_le_coe]; norm_num),
    min_eq_left (by rw [← NNReal.coe_le_coe]; norm_num), one_mul]

/-- The constant integrand: `∫_0^t 1 dB = B t - B 0`. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (t : ℝ≥0) :
    itoIntegral P F B (fun _ _ ↦ 1) t =ᵐ[P] fun ω ↦ B t ω - B 0 ω := by
  filter_upwards [itoIntegral_deterministic_eq hB hBF hInd (g := fun _ ↦ (1 : ℝ))
    contDiff_const t] with ω hω
  simpa using hω

/-- With `θ = 0` the Itô form of the Ornstein–Uhlenbeck solution is `X₀ + σ ∫_0^t dB`, equal to
`X₀ + σ (B t - B 0)`. -/
example (hB : IsBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (σ : ℝ) (X₀ : Ω → ℝ) (t : ℝ≥0) :
    (fun ω ↦ X₀ ω + σ * itoIntegral P F B (fun _ _ ↦ 1) t ω) =ᵐ[P]
      fun ω ↦ X₀ ω + σ * (B t ω - B 0 ω) := by
  filter_upwards [ito_ou_solution_eq_ouPathSolution hB hBF hInd 0 σ X₀ t] with ω hω
  simpa [ouPathSolution, Real.toNNReal_coe] using hω

/-- The Itô isometry instantiated on an elementary integrand. -/
example (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) (t : ℝ≥0) :
    ∫⁻ ω, ‖itoIntegral P F B (one12 F).toProcess t ω‖ₑ ^ 2 ∂P =
      ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖(one12 F).toProcess u.toNNReal ω‖ₑ ^ 2) ∂P :=
  lintegral_itoIntegral_sq hB hBF hInd (isItoApproximable_toProcess P _ t)

/-- The martingale property instantiated on an elementary integrand. -/
example (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) :
    Martingale (itoIntegral P F B (one12 F).toProcess) F P :=
  martingale_itoIntegral hB hBF hInd fun t ↦ isItoApproximable_toProcess P _ t

/-- Junk value: on an integrand that is not Itô-approximable, `itoIntegralL2` is `0`. -/
example (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (h : ¬ IsItoApproximable P F H t) :
    itoIntegralL2 P F B H t = 0 := by
  simp [itoIntegralL2, h]

end MathlibExtTest.Probability.ItoIntegral
