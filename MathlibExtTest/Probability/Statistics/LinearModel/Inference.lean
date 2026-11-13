/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.Inference
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Statistics.LinearModel.Inference` -/

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

namespace MathlibExtTest.LinearModelInference

/-- A two-coordinate Gaussian linear form: `Z₀ + Z₁ ~ N(0, 2)`. -/
example : (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map (fun x => ![1, 1] ⬝ᵥ x) =
    gaussianReal 0 2 := by
  rw [pi_gaussianReal_map_dotProduct]
  congr 1
  norm_num [dotProduct, Fin.sum_univ_two]

/-! ### Intercept-only design with three observations -/

/-- Intercept-only design with three observations (as in the `Sampling` tests). -/
noncomputable def X₀ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun _ _ => 1

theorem gram_X₀ : X₀ᵀ * X₀ = Matrix.of fun _ _ => 3 := by
  ext i j
  simp [X₀, Matrix.mul_apply]

theorem isUnit_gram_X₀ : IsUnit (X₀ᵀ * X₀) := by
  rw [Matrix.isUnit_iff_isUnit_det, gram_X₀, Matrix.det_unique]
  simp

theorem gram_X₀_inv : (X₀ᵀ * X₀)⁻¹ = Matrix.of fun _ _ => 1 / 3 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [gram_X₀]
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply]

theorem olsMatrix_X₀ : olsMatrix X₀ = Matrix.of fun _ _ => 1 / 3 := by
  rw [olsMatrix_eq, gram_X₀_inv]
  ext i j
  simp [X₀, Matrix.mul_apply]

/-- The variance factor of the intercept is `1 / 3`: `Var(ȳ) = σ² / 3`. -/
theorem contrastVariance_X₀ : contrastVariance X₀ ![1] = 1 / 3 := by
  rw [contrastVariance, gram_X₀_inv]
  simp [mulVec, dotProduct]

example : 0 < contrastVariance X₀ ![1] := contrastVariance_pos isUnit_gram_X₀ (by simp)

/-- `B Mᵀ = 0` on the fixture. -/
example : olsMatrix X₀ * (residualMatrix X₀)ᵀ = 0 :=
  olsMatrix_mul_transpose_residualMatrix isUnit_gram_X₀

/-- The intercept `t` statistic is `(ȳ - β) / √((RSS / 2) · (1 / 3))`. -/
example (β : Fin 1 → ℝ) (y : Fin 3 → ℝ) :
    tStatistic X₀ ![1] β y = ((y 0 + y 1 + y 2) / 3 - β 0) /
      √((y - X₀ *ᵥ olsEstimator X₀ y) ⬝ᵥ (y - X₀ *ᵥ olsEstimator X₀ y) / 2 * (1 / 3)) := by
  rw [tStatistic, contrastVariance_X₀]
  congr 1
  · simp only [olsEstimator, olsMatrix_X₀, mulVec, dotProduct, Fin.sum_univ_one,
      Fin.sum_univ_three, of_apply, Pi.sub_apply, Matrix.cons_val_zero]
    ring

/-! ### The Gaussian fixture: `ε = σ Z` with `Z` standard normal on `ℝ³` -/

variable (σ : ℝ)

theorem hasLaw_std (hσ : 0 < σ) :
    HasLaw (fun z : Fin 3 → ℝ => σ⁻¹ • (σ • z)) (Measure.pi fun _ : Fin 3 => gaussianReal 0 1)
      (Measure.pi fun _ : Fin 3 => gaussianReal 0 1) := by
  simp only [smul_smul, inv_mul_cancel₀ hσ.ne', one_smul]
  exact HasLaw.id

/-- The sample mean is independent of the residual vector. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) :
    IndepFun (fun z : Fin 3 → ℝ => olsEstimator X₀ (X₀ *ᵥ β + σ • z))
      (fun z => X₀ *ᵥ β + σ • z - X₀ *ᵥ olsEstimator X₀ (X₀ *ᵥ β + σ • z))
      (Measure.pi fun _ : Fin 3 => gaussianReal 0 1) :=
  indepFun_olsEstimator_residual isUnit_gram_X₀ β hσ (hasLaw_std σ hσ)

/-- The standardized sample mean `(ȳ - β) / (σ / √3)` is standard normal. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) :
    HasLaw (fun z : Fin 3 → ℝ => ![1] ⬝ᵥ (olsEstimator X₀ (X₀ *ᵥ β + σ • z) - β) /
        (σ * √(contrastVariance X₀ ![1]))) (gaussianReal 0 1)
      (Measure.pi fun _ : Fin 3 => gaussianReal 0 1) :=
  hasLaw_contrast_div isUnit_gram_X₀ β hσ (hasLaw_std σ hσ) (by simp)

/-- The intercept `t` statistic of three normal observations has law `t₂`. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) :
    HasLaw (fun z : Fin 3 → ℝ => tStatistic X₀ ![1] β (X₀ *ᵥ β + σ • z)) (studentTMeasure 2)
      (Measure.pi fun _ : Fin 3 => gaussianReal 0 1) := by
  simpa using hasLaw_tStatistic isUnit_gram_X₀ (by simp) β hσ (hasLaw_std σ hσ)
    (a := ![1]) (by simp)

/-- Coverage at `c = 1`: `P(|T| ≤ 1) = t₂([-1, 1])`. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) :
    (Measure.pi fun _ : Fin 3 => gaussianReal 0 1).real
        {z | |tStatistic X₀ ![1] β (X₀ *ᵥ β + σ • z)| ≤ 1} =
      (studentTMeasure 2).real (Set.Icc (-1) 1) := by
  simpa using measureReal_abs_tStatistic_le isUnit_gram_X₀ (by simp) β hσ (hasLaw_std σ hσ)
    (a := ![1]) (by simp) 1

end MathlibExtTest.LinearModelInference

/-! ### The one-sample `t` statistic -/

namespace MathlibExtTest.LinearModelInferenceOneSampleT

open MeasureTheory ProbabilityTheory Real

/-- Smallest admissible sample, `n = 2`: the statistic of two standard normal observations has
law `t₁` (the Cauchy law). Uses the pinned theorem. -/
example : (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map
    (fun x : Fin 2 → ℝ => √(2 : ℕ) * ((∑ i, x i) / (2 : ℕ) - 0) /
      √((∑ i, (x i - (∑ j, x j) / (2 : ℕ)) ^ 2) / (((2 : ℕ) : ℝ) - 1))) =
    studentTMeasure 1 := by
  exact map_tStatistic_pi_gaussianReal le_rfl 0 one_ne_zero

/-- Boundary `n = 1`: the target `studentTMeasure 0` is the zero measure, so `2 ≤ n` cannot be
weakened to `1 ≤ n`. -/
example : ¬ IsProbabilityMeasure (studentTMeasure 0) := by
  intro h
  have h0 : studentTMeasure 0 = 0 := by
    simp [studentTMeasure]
  exact IsProbabilityMeasure.ne_zero _ h0

/-- Boundary `v = 0`: the sample is a.s. constant, the statistic is `0 / 0 = 0`, and its law is
the Dirac mass at `0`, not a `t` law, so `v ≠ 0` cannot be dropped. -/
example (μ : ℝ) : (Measure.pi fun _ : Fin 2 => gaussianReal μ 0).map
    (fun x : Fin 2 → ℝ => √(2 : ℕ) * ((∑ i, x i) / (2 : ℕ) - μ) /
      √((∑ i, (x i - (∑ j, x j) / (2 : ℕ)) ^ 2) / (((2 : ℕ) : ℝ) - 1))) =
    Measure.dirac 0 := by
  have hpi : (Measure.pi fun _ : Fin 2 => gaussianReal μ 0) = Measure.dirac fun _ => μ := by
    simp_rw [gaussianReal_zero_var]
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs), Fin.prod_univ_two,
      Measure.dirac_apply' _ (hs 0), Measure.dirac_apply' _ (hs 1)]
    by_cases h0 : μ ∈ s 0 <;> by_cases h1 : μ ∈ s 1 <;> simp [Fin.forall_fin_two, h0, h1]
  rw [hpi, Measure.map_dirac]
  congr 1
  norm_num

end MathlibExtTest.LinearModelInferenceOneSampleT
