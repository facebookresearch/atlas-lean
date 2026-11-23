/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.WaldDiagonalTerms
public import MathlibExtTest.Probability.WaldDiagonalTerms
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section
open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.WaldDiagonalTerms
open MathlibExtTest.Probability.WaldDiagonalTerms

namespace MathlibExtTest.Probability.WaldDiagonalTermsCanonicalTests

/-- Signed increments exercise canonical integrability without a nonnegativity premise. -/
theorem signed_canonical_integrable :
    Integrable (fun ω : ℝ => ∑ i ∈ Finset.range 2,
      (fun (_ : ℕ) (_ : ℝ) => (-3 : ℝ)) i ω) (Measure.dirac (0 : ℝ)) :=
  wald_integrable_stopped_sum
    (X := fun (_ : ℕ) (_ : ℝ) => (-3 : ℝ))
    (f := Filtration.const ℕ (⊥ : MeasurableSpace ℝ) bot_le) (T := fun _ => 2)
    (fun _ _ => IdentDistrib.refl aemeasurable_const) (integrable_const (-3 : ℝ))
    (isStoppingTime_const _ _) (fun _ => indep_bot_right _) (integrable_const (2 : ℝ))

/-- The diagonal sum for two increments -3 is 18, rather than the stopped square 36. -/
theorem signed_diagonal_value :
    (∫ ω : ℝ, (∑ i ∈ Finset.range 2,
      ((fun (_ : ℕ) (_ : ℝ) => (-3 : ℝ)) i ω)^2) ∂Measure.dirac (0 : ℝ)) = 18 := by
  have h := wald_diagonal_terms (μ := Measure.dirac (0 : ℝ))
    (X := fun (_ : ℕ) (_ : ℝ) => (-3 : ℝ))
    (f := Filtration.const ℕ (⊥ : MeasurableSpace ℝ) bot_le) (T := fun _ => 2)
    (fun _ _ => IdentDistrib.refl aemeasurable_const) (by simp)
    (isStoppingTime_const _ _) (fun _ => indep_bot_right _) (integrable_const (2 : ℝ))
  calc
    _ = (∫ _ : ℝ, (-3 : ℝ)^2 ∂Measure.dirac (0 : ℝ)) *
        (∫ _ : ℝ, (2 : ℝ) ∂Measure.dirac (0 : ℝ)) := h
    _ = 18 := by norm_num

/-- The standard Gaussian coordinate has mean zero. -/
theorem coordinate_mean_zero : (∫ ω, coord 0 ω ∂gaussPi) = 0 := by
  have hId : IdentDistrib (coord 0) id gaussPi (gaussianReal (0 : ℝ) 1) :=
    ⟨(coord_measurable 0).aemeasurable, aemeasurable_id,
      by rw [coord_map 0, Measure.map_id]⟩
  have h := hId.integral_eq
  simpa using h

/-- Repeating a nondegenerate coordinate gives a family that is not jointly independent. -/
theorem repeated_coordinate_not_iIndep : ¬ iIndepFun (fun _ : ℕ => coord 0) gaussPi := by
  intro h
  have hind : IndepFun (coord 0) (coord 0) gaussPi :=
    h.indepFun (by norm_num : (0 : ℕ) ≠ 1)
  have hfactor := hind.integral_mul_eq_mul_integral
    (coord_measurable 0).aestronglyMeasurable (coord_measurable 0).aestronglyMeasurable
  have hsquare : (∫ ω, coord 0 ω * coord 0 ω ∂gaussPi) = 1 := by
    simpa only [pow_two] using coord_sq_integral
  change (∫ ω, coord 0 ω * coord 0 ω ∂gaussPi) =
    (∫ ω, coord 0 ω ∂gaussPi) * (∫ ω, coord 0 ω ∂gaussPi) at hfactor
  rw [hsquare, coordinate_mean_zero, zero_mul] at hfactor
  norm_num at hfactor

/-- The diagonal identity applies to that dependent family with the trivial filtration. -/
theorem repeated_coordinate_diagonal_value :
    (∫ ω, (∑ _i ∈ Finset.range 2, (coord 0 ω)^2) ∂gaussPi) = 2 := by
  have h := wald_diagonal_terms (X := fun _ : ℕ => coord 0)
    (f := Filtration.const ℕ (⊥ : MeasurableSpace (ℕ → ℝ)) bot_le) (T := fun _ => 2)
    (fun _ _ => IdentDistrib.refl (coord_measurable 0).aemeasurable)
    coord_sq_integrable (isStoppingTime_const _ _)
    (fun _ => indep_bot_right _) (integrable_const (2 : ℝ))
  calc
    _ = (∫ ω, (coord 0 ω)^2 ∂gaussPi) * (∫ _ : ℕ → ℝ, (2 : ℝ) ∂gaussPi) := h
    _ = 2 := by rw [coord_sq_integral]; simp

/-- Integrability likewise needs no joint-independence hypothesis. -/
theorem repeated_coordinate_integrable :
    Integrable (fun ω => ∑ _i ∈ Finset.range 2, (coord 0 ω)^2) gaussPi :=
  integrable_stopped_sum_sq_diag (X := fun _ : ℕ => coord 0)
    (f := Filtration.const ℕ (⊥ : MeasurableSpace (ℕ → ℝ)) bot_le) (T := fun _ => 2)
    (fun _ _ => IdentDistrib.refl (coord_measurable 0).aemeasurable)
    coord_sq_integrable (isStoppingTime_const _ _)
    (fun _ => indep_bot_right _) (integrable_const (2 : ℝ))

end MathlibExtTest.Probability.WaldDiagonalTermsCanonicalTests
