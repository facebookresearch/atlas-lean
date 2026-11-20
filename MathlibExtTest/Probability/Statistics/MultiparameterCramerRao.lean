/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultiparameterCramerRao
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Algebra.Order.Star.Real

/-!
# Tests for the Cramér–Rao inequality with a vector parameter

The two-point model `p θ = ((1 + sin θ₀) / 2, (1 - sin θ₀) / 2)` with a parameter
`θ ∈ ℝ¹ = EuclideanSpace ℝ (Fin 1)` satisfies every hypothesis of `cramerRao_multiparameter` at
`θ = 0`, including positive definiteness of the Fisher information matrix (here `[1]`), so the
hypotheses are jointly satisfiable; the indicator estimator of `(1 + sin θ₀) / 2` has variance
`1 / 4`, and the bound `∇gᵀ I⁻¹ ∇g = 1 / 4` is attained.
-/

@[expose] public section

open MeasureTheory Filter Topology Matrix
open MathlibExt.Probability.Statistics.MultiparameterCramerRao

namespace MathlibExtTest.Probability.Statistics.MultiparameterCramerRao

/-- The signs `+1, -1` of the two outcomes. -/
noncomputable def sgn : Fin 2 → ℝ := ![1, -1]

/-- The two-point family `p θ x = (1 + sgn x * sin θ₀) / 2` on `ℝ¹`. -/
noncomputable def pE (θ : EuclideanSpace ℝ (Fin 1)) (x : Fin 2) : ℝ :=
  (1 + sgn x * Real.sin (θ 0)) / 2

/-- The indicator of the first outcome. -/
noncomputable def tInd (x : Fin 2) : ℝ := (1 + sgn x) / 2

/-- The estimand `g θ = (1 + sin θ₀) / 2`. -/
noncomputable def gE (θ : EuclideanSpace ℝ (Fin 1)) : ℝ := (1 + Real.sin (θ 0)) / 2

/-- The coordinate projection `ℝ¹ → ℝ`. -/
noncomputable abbrev π0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj 0

theorem pE_nonneg (θ : EuclideanSpace ℝ (Fin 1)) (x : Fin 2) : 0 ≤ pE θ x := by
  fin_cases x <;> simp [pE, sgn] <;> linarith [Real.neg_one_le_sin (θ 0), Real.sin_le_one (θ 0)]

theorem hasFDerivAt_pE (x : Fin 2) :
    HasFDerivAt (fun θ => pE θ x) ((sgn x / 2) • π0) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (1 + sgn x * Real.sin t) / 2) (sgn x * Real.cos 0 / 2)
      ((0 : EuclideanSpace ℝ (Fin 1)) 0) := by
    simpa using (((Real.hasDerivAt_sin 0).const_mul (sgn x)).const_add 1).div_const 2
  have h := HasDerivAt.comp_hasFDerivAt (0 : EuclideanSpace ℝ (Fin 1)) h1 π0.hasFDerivAt
  simpa [Real.cos_zero, Function.comp_def, pE] using h

theorem hasFDerivAt_gE : HasFDerivAt gE ((1 / 2 : ℝ) • π0) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (1 + Real.sin t) / 2) (Real.cos 0 / 2)
      ((0 : EuclideanSpace ℝ (Fin 1)) 0) := by
    simpa using ((Real.hasDerivAt_sin 0).const_add 1).div_const 2
  have h := HasDerivAt.comp_hasFDerivAt (0 : EuclideanSpace ℝ (Fin 1)) h1 π0.hasFDerivAt
  unfold gE
  simpa [Real.cos_zero, Function.comp_def] using h

theorem fderiv_pE (x : Fin 2) : fderiv ℝ (fun θ => pE θ x) 0 = (sgn x / 2) • π0 :=
  (hasFDerivAt_pE x).fderiv

theorem integral_pE (θ : EuclideanSpace ℝ (Fin 1)) : ∫ x, pE θ x ∂Measure.count = 1 := by
  simp [pE, sgn, Fin.sum_univ_two]; ring

theorem integral_tInd_pE (θ : EuclideanSpace ℝ (Fin 1)) :
    ∫ x, tInd x * pE θ x ∂Measure.count = gE θ := by
  simp [pE, sgn, tInd, gE, Fin.sum_univ_two]

/-- The Fisher information matrix of the model at `0` is the `1 × 1` identity. -/
theorem fisherMatrix_eq_one :
    (Matrix.of fun i j : Fin 1 =>
      ∫ x, fderiv ℝ (fun θ' => pE θ' x) 0 (EuclideanSpace.single i 1) *
        fderiv ℝ (fun θ' => pE θ' x) 0 (EuclideanSpace.single j 1) / pE 0 x ∂Measure.count) =
      1 := by
  ext i j
  fin_cases i; fin_cases j
  simp only [fderiv_pE]
  simp [integral_count, Fin.sum_univ_two, pE, sgn]
  norm_num

/-- Every hypothesis of `cramerRao_multiparameter` holds for the two-point model at `θ = 0`. -/
theorem cramerRao_multiparameter_pE :
    (fun i => fderiv ℝ gE 0 (EuclideanSpace.single i 1)) ⬝ᵥ
        ((Matrix.of fun i j : Fin 1 =>
          ∫ x, fderiv ℝ (fun θ' => pE θ' x) 0 (EuclideanSpace.single i 1) *
            fderiv ℝ (fun θ' => pE θ' x) 0 (EuclideanSpace.single j 1) / pE 0 x
              ∂Measure.count)⁻¹ *ᵥ
          (fun i => fderiv ℝ gE 0 (EuclideanSpace.single i 1))) ≤
      ∫ x, (tInd x - gE 0) ^ 2 * pE 0 x ∂Measure.count := by
  refine cramerRao_multiparameter (fun θ x => pE_nonneg θ x)
    (Eventually.of_forall integral_pE) (fun x => (hasFDerivAt_pE x).differentiableAt)
    (fun _ => (Integrable.of_finite).aestronglyMeasurable) (fun _ => Integrable.of_finite)
    (by rw [fisherMatrix_eq_one]; exact Matrix.PosDef.one)
    (Integrable.of_finite).aestronglyMeasurable Integrable.of_finite
    (Eventually.of_forall integral_tInd_pE) ?_ ?_
  · have h : (fun θ' => ∫ x, pE θ' x ∂Measure.count) = fun _ => 1 := funext integral_pE
    rw [h]
    simp only [fderiv_pE, integral_count, Fin.sum_univ_two]
    convert hasFDerivAt_const (1 : ℝ) (0 : EuclideanSpace ℝ (Fin 1)) using 1
    ext v
    simp [sgn]
    ring
  · have h : (fun θ' => ∫ x, tInd x * pE θ' x ∂Measure.count) = gE := funext integral_tInd_pE
    rw [h]
    simp only [fderiv_pE, integral_count, Fin.sum_univ_two]
    convert hasFDerivAt_gE using 1
    ext v
    simp [tInd, sgn]

/-- The bound is attained: both sides equal `1 / 4`. -/
theorem cramerRao_multiparameter_pE_eq :
    (fun i => fderiv ℝ gE 0 (EuclideanSpace.single i 1)) ⬝ᵥ
        ((Matrix.of fun i j : Fin 1 =>
          ∫ x, fderiv ℝ (fun θ' => pE θ' x) 0 (EuclideanSpace.single i 1) *
            fderiv ℝ (fun θ' => pE θ' x) 0 (EuclideanSpace.single j 1) / pE 0 x
              ∂Measure.count)⁻¹ *ᵥ
          (fun i => fderiv ℝ gE 0 (EuclideanSpace.single i 1))) =
      ∫ x, (tInd x - gE 0) ^ 2 * pE 0 x ∂Measure.count := by
  rw [fisherMatrix_eq_one, inv_one, one_mulVec, hasFDerivAt_gE.fderiv]
  simp [dotProduct, tInd, gE, pE, sgn, integral_count, Fin.sum_univ_two]
  norm_num

end MathlibExtTest.Probability.Statistics.MultiparameterCramerRao
