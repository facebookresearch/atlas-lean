/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Generalized least squares: Aitken's theorem

For a design matrix `X` and a positive definite noise covariance `V` with `Xᵀ V⁻¹ X` invertible,
the generalized least-squares (GLS) matrix `B = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` satisfies `B X = 1`, so
`B y` is an unbiased estimator of `b` in `y = X b + e`, and its covariance
`B V Bᵀ = (Xᵀ V⁻¹ X)⁻¹` is minimal among linear unbiased estimators: `A V Aᵀ - B V Bᵀ` is
positive semidefinite for every `A` with `A X = 1` (Aitken 1936). The linear-algebra statement
is exact; the covariance of a linear estimator `A y` with `Cov e = V` is `A V Aᵀ`. With `V = 1`
this is the Gauss–Markov theorem of `MathlibExt.Probability.Statistics.GaussMarkov`.

## Main results

* `glsMatrix`: the GLS matrix `(Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`.
* `glsMatrix_mul_self`: unbiasedness, `B X = 1`.
* `glsMatrix_mul_mul_transpose`: the GLS covariance `B V Bᵀ = (Xᵀ V⁻¹ X)⁻¹`.
* `aitken`: `A V Aᵀ - B V Bᵀ` is positive semidefinite for every `A` with `A X = 1`.

## References

* A. C. Aitken, *On least squares and linear combination of observations*, Proc. Roy. Soc.
  Edinburgh 55 (1936), 42–48.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Probability.Statistics.GeneralizedLeastSquares

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-- The generalized least-squares matrix `(Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`; `glsMatrix X V *ᵥ y` is the GLS
estimate of `b` in `y = X b + e` with `Cov e = V`. -/
noncomputable def glsMatrix (X : Matrix m k ℝ) (V : Matrix m m ℝ) : Matrix k m ℝ :=
  (Xᵀ * V⁻¹ * X)⁻¹ * Xᵀ * V⁻¹

variable {X : Matrix m k ℝ} {V : Matrix m m ℝ}

/-- The GLS estimator is unbiased: `B X = 1` when `Xᵀ V⁻¹ X` is invertible. -/
theorem glsMatrix_mul_self (hX : IsUnit (Xᵀ * V⁻¹ * X)) : glsMatrix X V * X = 1 := by
  rw [glsMatrix, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hX)]

private theorem glsMatrix_mul_eq (hV : V.PosDef) :
    glsMatrix X V * V = (Xᵀ * V⁻¹ * X)⁻¹ * Xᵀ := by
  rw [glsMatrix, Matrix.mul_assoc _ V⁻¹, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit), Matrix.mul_one]

private theorem transpose_inv_of_posDef (hV : V.PosDef) : (V⁻¹)ᵀ = V⁻¹ := by
  have h : Vᵀ = V := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hV.isHermitian.eq
  rw [Matrix.transpose_nonsing_inv, h]

/-- The covariance of the GLS estimator: `B V Bᵀ = (Xᵀ V⁻¹ X)⁻¹`. -/
theorem glsMatrix_mul_mul_transpose (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) :
    glsMatrix X V * V * (glsMatrix X V)ᵀ = (Xᵀ * V⁻¹ * X)⁻¹ := by
  have hW : ((Xᵀ * V⁻¹ * X)⁻¹)ᵀ = (Xᵀ * V⁻¹ * X)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, transpose_inv_of_posDef hV, Matrix.mul_assoc]
  rw [glsMatrix_mul_eq hV, glsMatrix, Matrix.transpose_mul, Matrix.transpose_mul,
    transpose_inv_of_posDef hV, hW, Matrix.transpose_transpose]
  rw [show (Xᵀ * V⁻¹ * X)⁻¹ * Xᵀ * (V⁻¹ * (X * (Xᵀ * V⁻¹ * X)⁻¹)) =
      (Xᵀ * V⁻¹ * X)⁻¹ * (Xᵀ * V⁻¹ * X) * (Xᵀ * V⁻¹ * X)⁻¹ by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hX), Matrix.one_mul]

/-- **Aitken's theorem**: the GLS estimator has minimal covariance among linear unbiased
estimators: for every `A` with `A X = 1`, `A V Aᵀ - B V Bᵀ` is positive semidefinite, where
`B = glsMatrix X V`. -/
theorem aitken (hV : V.PosDef) (hX : IsUnit (Xᵀ * V⁻¹ * X)) (A : Matrix k m ℝ)
    (hA : A * X = 1) :
    (A * V * Aᵀ - glsMatrix X V * V * (glsMatrix X V)ᵀ).PosSemidef := by
  set B := glsMatrix X V with hB
  have hVt : Vᵀ = V := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hV.isHermitian.eq
  have hDX : (A - B) * X = 0 := by rw [Matrix.sub_mul, hA, hB, glsMatrix_mul_self hX, sub_self]
  have hBVD : B * V * (A - B)ᵀ = 0 := by
    rw [hB, glsMatrix_mul_eq hV, Matrix.mul_assoc, ← Matrix.transpose_mul, hDX,
      Matrix.transpose_zero, Matrix.mul_zero]
  have hDVB : (A - B) * V * Bᵀ = 0 := by
    have h := congrArg Matrix.transpose hBVD
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hVt,
      Matrix.transpose_zero, ← Matrix.mul_assoc] at h
  have key : A * V * Aᵀ - B * V * Bᵀ = (A - B) * V * (A - B)ᵀ := by
    have hA' : A = (A - B) + B := (sub_add_cancel A B).symm
    have e1 : A * V * Aᵀ = ((A - B) + B) * V * ((A - B) + B)ᵀ := by rw [← hA']
    rw [e1, Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, hBVD, hDVB]
    abel
  rw [key]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    hV.posSemidef.mul_mul_conjTranspose_same (A - B)

end MathlibExt.Probability.Statistics.GeneralizedLeastSquares
