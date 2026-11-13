/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Calibration

/-!

# Tests for analytical calibration

-/

@[expose] public section

open Chemistry.Calibration MathlibExt.Probability.FiniteProbability
  MathlibExt.Probability.Statistics.LinearModel Matrix

namespace PhyslibExtTest.Chemistry.Calibration

/-!

## A. Four-standard calibration

-/

/-- Standard concentrations of the four-standard example. -/
noncomputable def stdX : Fin 4 → ℝ :=
  ![0, 1, 2, 3]

/-- Measured responses of the four-standard example. -/
noncomputable def stdY : Fin 4 → ℝ :=
  ![1, 3, 4, 6]

example : calibrationSlope stdX stdY = 8 / 5 := by
  simp only [calibrationSlope, olsSlope, sxy, sampleMean_eq_sum_div, Fin.sum_univ_four]
  norm_num [stdX, stdY]

example : calibrationIntercept stdX stdY = 11 / 10 := by
  simp only [calibrationIntercept, olsIntercept, olsSlope, sxy,
    sampleMean_eq_sum_div, Fin.sum_univ_four]
  norm_num [stdX, stdY]

example : 0 < sxy stdX stdX := by
  simp only [sxy, sampleMean_eq_sum_div, Fin.sum_univ_four]
  norm_num [stdX]

example (a b : ℝ) : rssLine stdX stdY (calibrationIntercept stdX stdY)
    (calibrationSlope stdX stdY) ≤ rssLine stdX stdY a b := by
  have hsxx : 0 < sxy stdX stdX := by
    simp only [sxy, sampleMean_eq_sum_div, Fin.sum_univ_four]
    norm_num [stdX]
  exact ((calibration_unique_minimizer_iff stdX stdY).mpr hsxx a b).1

example (a b : ℝ)
    (hle : rssLine stdX stdY a b ≤ rssLine stdX stdY (calibrationIntercept stdX stdY)
      (calibrationSlope stdX stdY)) :
    a = calibrationIntercept stdX stdY ∧ b = calibrationSlope stdX stdY := by
  have hsxx : 0 < sxy stdX stdX := by
    simp only [sxy, sampleMean_eq_sum_div, Fin.sum_univ_four]
    norm_num [stdX]
  exact ((calibration_unique_minimizer_iff stdX stdY).mpr hsxx a b).2 hle

example : ∑ i, (stdY i - (11 / 10 + (8 / 5) * stdX i)) = 0 := by
  simp only [Fin.sum_univ_four]
  norm_num [stdX, stdY]

example : ∑ i, stdX i * (stdY i - (11 / 10 + (8 / 5) * stdX i)) = 0 := by
  simp only [Fin.sum_univ_four]
  norm_num [stdX, stdY]

example : ∑ i, (stdY i - (calibrationIntercept stdX stdY +
    calibrationSlope stdX stdY * stdX i)) = 0 :=
  calibration_sum_resid stdX stdY

example : ∑ i, stdX i * (stdY i - (calibrationIntercept stdX stdY +
    calibrationSlope stdX stdY * stdX i)) = 0 :=
  calibration_sum_mul_resid stdX stdY

/-!

## B. Gauss-Markov example

-/

/-- Regressor of the Gauss-Markov example design. -/
noncomputable def gmX : Fin 3 → ℝ :=
  ![0, 1, 2]

/-- Design matrix of the Gauss-Markov example: rows `(1, x i)`. -/
noncomputable def gmDesign : Matrix (Fin 3) (Fin 2) ℝ :=
  designMatrix gmX

/-- True coefficients of the Gauss-Markov example. -/
noncomputable def gmBeta : Fin 2 → ℝ :=
  ![5, 2]

/-- Error distribution weight: uniform on four outcomes. -/
noncomputable def gmP : Fin 4 → ℝ :=
  fun _ => 1 / 4

/-- Errors of the Gauss-Markov example: Hadamard-pattern outcomes with unit covariance. -/
noncomputable def gmErr : Fin 4 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

/-- Responses of the Gauss-Markov example. -/
noncomputable def gmY : Fin 4 → Fin 3 → ℝ :=
  fun ω => gmDesign *ᵥ gmBeta + gmErr ω

/-- A nontrivial alternative linear estimator matrix. -/
noncomputable def gmA : Matrix (Fin 2) (Fin 3) ℝ :=
  !![11 / 6, -5 / 3, 5 / 6; -1 / 2, 0, 1 / 2]

/-- First error basis vector, selecting the `(0, 0)` entry of the OLS matrix. -/
noncomputable def gmE0 : Fin 3 → ℝ :=
  ![1, 0, 0]

lemma gm_sxx : 0 < sxy gmX gmX := by
  simp only [sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
  norm_num [gmX]

lemma gm_hp1 : ∑ ω, gmP ω = 1 := by
  simp only [gmP, Fin.sum_univ_four]
  norm_num

lemma gm_hmean : ∀ i, expectation gmP (fun ω => gmErr ω i) = 0 := by
  intro i
  fin_cases i <;> simp only [expectation, Fin.sum_univ_four] <;> norm_num [gmP, gmErr]

lemma gm_hcov : covMatrix gmP gmErr = (1 : ℝ) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [covMatrix_apply, covariance, expectation, Fin.sum_univ_four, gmP, gmErr] <;>
    norm_num

lemma gm_hmodel : ∀ ω, gmY ω = gmDesign *ᵥ gmBeta + gmErr ω :=
  fun _ => rfl

lemma gm_hX : IsUnit (gmDesignᵀ * gmDesign) := by
  show IsUnit ((designMatrix gmX)ᵀ * designMatrix gmX)
  exact (isUnit_gram_designMatrix_iff gmX).mpr gm_sxx

lemma gm_hA : gmA * gmDesign = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gmA, gmDesign, designMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
    norm_num [gmX]

lemma gm_B00 : olsMatrix gmDesign 0 0 = 5 / 6 := by
  have hB00 : olsEstimator gmDesign gmE0 0 = olsMatrix gmDesign 0 0 := by
    simp [olsEstimator, Matrix.mulVec, dotProduct, Fin.sum_univ_three, gmE0]
  have hest : olsEstimator gmDesign gmE0 =
      ![olsIntercept gmX gmE0, olsSlope gmX gmE0] := by
    show olsEstimator (designMatrix gmX) gmE0 = _
    exact olsEstimator_designMatrix gm_sxx gmE0
  have h0 : olsEstimator gmDesign gmE0 0 = olsIntercept gmX gmE0 := by
    rw [hest, Matrix.cons_val_zero]
  rw [hB00] at h0
  rw [h0]
  simp only [olsIntercept, olsSlope, sxy, sampleMean_eq_sum_div, Fin.sum_univ_three]
  norm_num [gmX, gmE0]

lemma gm_A_ne_ols : gmA ≠ olsMatrix gmDesign := by
  intro hcon
  have h00 : gmA 0 0 = olsMatrix gmDesign 0 0 := by rw [hcon]
  rw [gm_B00] at h00
  norm_num [gmA] at h00

example (j : Fin 2) :
    expectation gmP (fun ω => olsEstimator gmDesign (gmY ω) j) = gmBeta j :=
  expectation_olsEstimator_calibration gmDesign gm_hX gmP gmErr gmY gmBeta gm_hp1
    gm_hmean gm_hmodel j

example (j : Fin 2) : expectation gmP (fun ω => (gmA *ᵥ gmY ω) j) = gmBeta j :=
  expectation_linearUnbiased_calibration gmDesign gmP gmErr gmY gmBeta gm_hp1
    gm_hmean gm_hmodel gmA gm_hA j

example : (covMatrix gmP (fun ω => gmA *ᵥ gmY ω) -
    covMatrix gmP (fun ω => olsEstimator gmDesign (gmY ω))).PosSemidef :=
  calibration_blue_covariance gmDesign gm_hX gmP gmErr 1 gm_hp1 gm_hcov gmY gmBeta
    gm_hmodel gmA gm_hA

/-!

## C. Inverse prediction

-/

/-- Diagonal input covariance: response, intercept and slope variances. -/
noncomputable def ipV : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1 / 25, 0, 0], ![0, 1 / 100, 0], ![0, 0, 1 / 400]]

lemma ip_h00 : ipV 0 0 = 1 / 25 := by
  simp [ipV]

lemma ip_h11 : ipV 1 1 = 1 / 100 := by
  simp [ipV]

lemma ip_h22 : ipV 2 2 = 1 / 400 := by
  simp [ipV]

lemma ip_hoff : ∀ i j, i ≠ j → ipV i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [ipV]

example : inversePrediction 1 2 7 = 3 := by
  norm_num [inversePrediction]

example : 2 * inversePrediction 1 2 7 + 1 = 7 :=
  inversePrediction_mul 1 2 7 (by norm_num)

example : inversePredictionGradient 1 2 7 = ![1 / 2, -1 / 2, -3 / 2] := by
  ext i
  fin_cases i <;> simp [inversePredictionGradient]; norm_num

example : inversePredictionFirstOrderVariance (inversePredictionGradient 1 2 7) ipV
    = 29 / 1600 := by
  rw [firstOrderInversePredictionVariance_gradient_diagonal 1 2 7 ipV _ _ _ ip_h00
    ip_h11 ip_h22 ip_hoff]
  norm_num

/-!

## D. Standard addition and internal standard

-/

example : standardAdditionUnknown 10 2 = 5 :=
  standardAdditionUnknown_eq 5 10 2 0 (fun s => 2 * (5 + s)) (fun s => rfl)
    (fun s => by ring) (by norm_num)

example : (5 : ℝ) = (11 - 1) / 2 :=
  standardAddition_unknown_eq 5 1 11 2 0 (fun s => 1 + 2 * (5 + s)) (fun s => rfl)
    (fun s => by ring) (by norm_num)

example : internalStandardRatio 100 50 = 2 := by
  norm_num [internalStandardRatio]

example : internalStandardRatio (1.2 * 100) (1.2 * 50) = internalStandardRatio 100 50 :=
  internalStandardRatio_commonDrift 100 50 1.2 (by norm_num) (by norm_num)

example : internalStandardRatio (1.2 * 100) (1.2 * 50) = 2 := by
  norm_num [internalStandardRatio]

example : internalStandardRatio (1.2 * 100) (0.8 * 50) =
    (1.2 / 0.8) * internalStandardRatio 100 50 :=
  internalStandardRatio_independentDrift 100 50 1.2 0.8 (by norm_num) (by norm_num)

example : internalStandardRatio (1.2 * 100) (0.8 * 50) ≠ internalStandardRatio 100 50 :=
  internalStandardRatio_independentDrift_ne 100 50 1.2 0.8 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end PhyslibExtTest.Chemistry.Calibration
