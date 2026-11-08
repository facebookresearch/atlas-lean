/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConvexSubGaussianComparison

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.ConvexSubGaussianComparison

namespace MathlibExtTest.Probability.ConvexSubGaussianComparison

theorem actual_dirac_zero_tail :
    IsOneSubGaussianTail (Measure.dirac (0 : ℝ)) (fun _ : ℝ => 0) :=
  IsOneSubGaussianTail.zero _

theorem actual_dirac_zero_convex :
    ConvexDominated (Measure.dirac (0 : ℝ)) (fun _ : ℝ => 0)
      (Measure.dirac (0 : ℝ)) (fun _ : ℝ => 0) :=
  ConvexDominated.refl _ _

theorem actual_dirac_zero_quadratic :
    Integrable (fun _ : ℝ => (0 : ℝ) ^ 2) (Measure.dirac (0 : ℝ)) ∧
      (∫ _ : ℝ, (0 : ℝ) ^ 2 ∂Measure.dirac (0 : ℝ)) = 0 := by
  exact ⟨integrable_const _, by simp⟩

theorem actual_populated_admissible_law :
    ∃ (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ),
      @IsOneSubGaussianTail ℝ _ μ hμ (fun _ : ℝ => 0) ∧
        ConvexDominated μ (fun _ : ℝ => 0) μ (fun _ : ℝ => 0) :=
  ⟨Measure.dirac 0, inferInstance, actual_dirac_zero_tail, actual_dirac_zero_convex⟩

theorem actual_standard_gaussian_mgf :
    HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) := by
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, ?_⟩
  intro t
  simp [mgf_fun_id_gaussianReal]

theorem actual_standard_gaussian_tail :
    IsOneSubGaussianTail (gaussianReal 0 1) (fun x : ℝ => x) := by
  exact IsOneSubGaussianTail.of_hasSubgaussianMGF measurable_id
    actual_standard_gaussian_mgf (by simp)

theorem actual_standard_gaussian_variance :
    Var[fun x : ℝ => x; gaussianReal 0 1] = 1 := by
  simp

theorem actual_standard_gaussian_quadratic :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) ∧
      (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  refine ⟨(memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).1
    (actual_standard_gaussian_mgf.memLp 2), ?_⟩
  have h := actual_standard_gaussian_variance
  rw [variance_eq_integral (X := fun x : ℝ => x)
    (μ := gaussianReal 0 1) measurable_id.aemeasurable] at h
  simpa using h

theorem actual_standard_gaussian_convex :
    ConvexDominated (gaussianReal 0 1) (fun x : ℝ => x) (gaussianReal 0 1)
      (fun x : ℝ => Real.sqrt (1 : ENNReal).toReal * x) := by
  simpa using ConvexDominated.refl (gaussianReal 0 1) (fun x : ℝ => x)

theorem actual_populated_nondegenerate_law :
    ∃ (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ),
      @IsOneSubGaussianTail ℝ _ μ hμ (fun x : ℝ => x) ∧
        Var[fun x : ℝ => x; μ] = 1 ∧
        ConvexDominated μ (fun x : ℝ => x) (gaussianReal 0 1)
          (fun x : ℝ => Real.sqrt (1 : ENNReal).toReal * x) :=
  ⟨gaussianReal 0 1, inferInstance, actual_standard_gaussian_tail,
    actual_standard_gaussian_variance, actual_standard_gaussian_convex⟩

theorem actual_dirac_strict_zero_event :
    (Measure.dirac (0 : ℝ)) {x : ℝ | |x| > 0} = 0 := by
  simp

theorem actual_dirac_nonstrict_zero_event :
    (Measure.dirac (0 : ℝ)) {x : ℝ | |x| ≥ 0} = 1 := by
  simp

example (x : ℝ) : gaussianPDFReal 0 1 x =
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal]

example {C : ENNReal} (hC : IsAdmissibleConstant C) : comparisonConstant ≤ C :=
  comparisonConstant_le_of_isAdmissibleConstant hC

example {C : ENNReal} (hC : IsAdmissibleConstant C) : (1 : ENNReal) ≤ C :=
  one_le_of_isAdmissibleConstant hC

example : (1 : ENNReal) ≤ comparisonConstant := one_le_comparisonConstant

example (C : ENNReal) (hC : ∀ D : ENNReal, IsAdmissibleConstant D → C ≤ D) :
    C ≤ comparisonConstant :=
  (le_comparisonConstant_iff C).2 hC

example : ¬IsAdmissibleConstant 0 := not_isAdmissibleConstant_zero

example : ¬IsAdmissibleConstant ⊤ := not_isAdmissibleConstant_top

theorem actual_admissible_elim_universe_one (C : ENNReal) (hC : IsAdmissibleConstant C) :
    ConvexDominated (Measure.dirac (ULift.up (0 : ℝ))) (fun _ : ULift ℝ => (0 : ℝ))
      (gaussianReal 0 1) (fun g : ℝ => Real.sqrt C.toReal * g) :=
  hC.elim _ _ (IsOneSubGaussianTail.zero _)

end MathlibExtTest.Probability.ConvexSubGaussianComparison
