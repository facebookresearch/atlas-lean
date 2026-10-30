/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Regression.GBLUP

@[expose] public section

/-!
# Tests for RR-BLUP = GBLUP = GP posterior mean
-/

set_option autoImplicit false

open Matrix
open Cslib.MachineLearning.LeastSquares Cslib.MachineLearning.GaussianProcessRegression
open Cslib.MachineLearning.GBLUP

namespace CSLibExtTest.MachineLearning.Regression.GBLUP

/-- Two individuals genotyped at one marker, both carrying one copy. -/
def Z₀ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]

/-- The genomic relationship matrix `ZZᵀ` of the example is the all-ones matrix. -/
example : Z₀ * Z₀ᵀ = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Z₀, Matrix.mul_apply]

/-- The marker kernel evaluates to `s` times the dot product of genotype vectors. -/
example : markerKernel 2 ![1, 0, 2] ![3, 5, 1] = 10 := by
  simp [markerKernel, dotProduct, Fin.sum_univ_three]
  norm_num

/-- The ridge marker effect in the example: `(ZᵀZ + I)⁻¹ Zᵀ y = (1 + 2) / 3 = 1` for `y = (1, 2)`
and `λ = 1`, computed through the GBLUP form. -/
example : ridgeEstimate Z₀ ![1, 2] 1 = ![1] := by
  have hZ : Z₀ᵀ * Z₀ + (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![3] := by
    ext i j
    fin_cases i; fin_cases j
    simp [Z₀, Matrix.mul_apply]
    norm_num
  rw [ridgeEstimate, hZ]
  ext i
  fin_cases i
  simp [Z₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

/-- RR-BLUP and GBLUP fitted values agree (instance of the push-through identity). -/
example (y : Fin 2 → ℝ) :
    Z₀ *ᵥ ridgeEstimate Z₀ y 1 =
      (Z₀ * Z₀ᵀ * (Z₀ * Z₀ᵀ + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹) *ᵥ y :=
  mulVec_ridgeEstimate Z₀ Z₀ y one_pos

/-- The GP predictive mean with the marker kernel (`s = 2`, `σ² = 1`) is RR-BLUP with
`λ = 1/2`. -/
example (Z' : Matrix (Fin 3) (Fin 1) ℝ) (y : Fin 2 → ℝ) :
    (kernelMatrix (markerKernel 2) Z' Z₀ *
        (kernelMatrix (markerKernel 2) Z₀ Z₀ + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹) *ᵥ
        y =
      Z' *ᵥ ridgeEstimate Z₀ y (1 / 2) :=
  gpMean_markerKernel_mulVec two_pos one_pos Z' Z₀ y

/-- The marker kernel with nonnegative variance is a covariance kernel. -/
example : (kernelMatrix (markerKernel 2) Z₀ Z₀).PosSemidef :=
  kernelMatrix_markerKernel_posSemidef zero_le_two Z₀

/-- Boundary case (junk value outside `λ > 0`): at `λ = 0` the GBLUP matrix `ZZᵀ` of the example
is singular, Lean's matrix inverse returns `0`, and the "GBLUP" fitted values are `0`, although
ridge regression at `λ = 0` (least squares) fits `y = (1, 1)` exactly. The identities above
require `λ > 0`. -/
example : (Z₀ * Z₀ᵀ * (Z₀ * Z₀ᵀ + (0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹) *ᵥ ![1, 1] = 0 ∧
    Z₀ *ᵥ ridgeEstimate Z₀ ![1, 1] 0 = ![1, 1] := by
  have hG : Z₀ * Z₀ᵀ + (0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 1; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Z₀, vecMul, dotProduct]
  have hR : Z₀ᵀ * Z₀ + (0 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![2] := by
    ext i j
    fin_cases i; fin_cases j
    simp [Z₀, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  have hdet : ¬ IsUnit (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp [Matrix.det_fin_two]
  constructor
  · rw [hG, Matrix.nonsing_inv_apply_not_isUnit _ hdet, Matrix.mul_zero, Matrix.zero_mulVec]
  · rw [ridgeEstimate, hR]
    ext i
    fin_cases i <;> simp [Z₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

end CSLibExtTest.MachineLearning.Regression.GBLUP
