/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.LinearHypothesis

/-!
# Tests for `MathlibExt.Probability.Statistics.LinearModel.LinearHypothesis`

The intercept-only design with the hypothesis "intercept = c": rank `1` and a `χ²₁` numerator
under `H₀`. A zero hypothesis row fails the full-row-rank hypothesis. For a single contrast the
numerator form is `(aᵀ b)² / (aᵀ G a)`.
-/

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

namespace MathlibExtTest.LinearModelLinearHypothesis

/-- Intercept-only design with three observations. -/
private def X₀ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- The hypothesis "intercept = c" as a `1 × 1` hypothesis matrix. -/
private def C₀ : Matrix (Fin 1) (Fin 1) ℝ := 1

private theorem isUnit_gram_X₀ : IsUnit (X₀ᵀ * X₀) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique, isUnit_iff_ne_zero]
  simp [X₀, Matrix.mul_apply]

private theorem isUnit_C₀ : IsUnit (C₀ * (X₀ᵀ * X₀)⁻¹ * C₀ᵀ) := by
  rw [C₀, transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.isUnit_nonsing_inv_iff]
  exact isUnit_gram_X₀

/-- The fixture's hypothesis matrix has rank `q = 1`. -/
example : (hypothesisMatrix X₀ C₀).rank = 1 := by
  rw [rank_hypothesisMatrix isUnit_gram_X₀ isUnit_C₀, Fintype.card_fin]

/-- Non-vacuity under `H₀` (here `c = C₀ β`): with `ε = σ • Z`, the numerator is `χ²₁`. -/
example {σ : ℝ} (hσ : 0 < σ) (β : Fin 1 → ℝ) :
    HasLaw (fun x : Fin 3 → ℝ => (C₀ *ᵥ olsEstimator X₀ (X₀ *ᵥ β + σ • x) - C₀ *ᵥ β) ⬝ᵥ
        ((C₀ * (X₀ᵀ * X₀)⁻¹ * C₀ᵀ)⁻¹ *ᵥ (C₀ *ᵥ olsEstimator X₀ (X₀ *ᵥ β + σ • x) - C₀ *ᵥ β)) /
          σ ^ 2)
      (chiSquareMeasure 1) (Measure.pi fun _ : Fin 3 => gaussianReal 0 1) := by
  have h := hasLaw_linearHypothesis_numerator (μ := Measure.pi fun _ : Fin 3 => gaussianReal 0 1)
    (ε := fun x : Fin 3 → ℝ => σ • x) isUnit_gram_X₀ isUnit_C₀ (by simp) β rfl hσ
    (by simp_rw [inv_smul_smul₀ hσ.ne']; exact HasLaw.id)
  rwa [Fintype.card_fin] at h

/-- A hypothesis matrix with a zero row is not full row rank, so `hC` excludes it. -/
example : ¬ IsUnit ((0 : Matrix (Fin 1) (Fin 1) ℝ) * (X₀ᵀ * X₀)⁻¹ *
    (0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) := by
  rw [Matrix.zero_mul, Matrix.zero_mul]
  exact not_isUnit_zero

/-- Single contrast `q = 1`, `C = aᵀ`: the numerator form is `(aᵀ b)² / (aᵀ G a)`, the square of
the standardized contrast used by the Atlas `t` statistic. -/
example {k : Type*} [Fintype k] [DecidableEq k] (G : Matrix k k ℝ) (a b : k → ℝ) :
    ((Matrix.of fun (_ : Fin 1) j => a j) *ᵥ b) ⬝ᵥ
        (((Matrix.of fun (_ : Fin 1) j => a j) * G * (Matrix.of fun (_ : Fin 1) j => a j)ᵀ)⁻¹ *ᵥ
          ((Matrix.of fun (_ : Fin 1) j => a j) *ᵥ b)) =
      (a ⬝ᵥ b) ^ 2 / (a ⬝ᵥ (G *ᵥ a)) := by
  have hAb : (Matrix.of fun (_ : Fin 1) j => a j) *ᵥ b = fun _ => a ⬝ᵥ b := by
    ext i
    simp [mulVec, dotProduct]
  have hAGA : (Matrix.of fun (_ : Fin 1) j => a j) * G * (Matrix.of fun (_ : Fin 1) j => a j)ᵀ =
      Matrix.of fun _ _ => a ⬝ᵥ (G *ᵥ a) := by
    ext i j
    rw [dotProduct_mulVec]
    simp [Matrix.mul_apply, vecMul, dotProduct]
  have hinv : ∀ d : ℝ, (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => d)⁻¹ =
      Matrix.of fun _ _ => d⁻¹ := by
    intro d
    ext i j
    rw [Matrix.inv_def, Matrix.adjugate_fin_one, Matrix.det_unique, Ring.inverse_eq_inv']
    simp [Subsingleton.elim i j]
  rw [hAb, hAGA, hinv]
  generalize a ⬝ᵥ b = x
  generalize a ⬝ᵥ (G *ᵥ a) = d
  simp [dotProduct, mulVec]
  ring

end MathlibExtTest.LinearModelLinearHypothesis
