/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.QR

@[expose] public section

open Matrix MathlibExt.LinearAlgebra.Matrix.QR

namespace MathlibExtTest.LinearAlgebra.Matrix.QR

/-- The identity is its own QR factorization, so by uniqueness the Gram–Schmidt factors of
the identity are `Q = R = I`. -/
example : qrQ (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∧ qrR (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  have h : LinearIndependent ℝ (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ := by
    rw [transpose_one]
    exact Matrix.linearIndependent_rows_of_det_ne_zero (by simp)
  have hup : (1 : Matrix (Fin 2) (Fin 2) ℝ).IsUpperTriangular := blockTriangular_one
  obtain ⟨hQ, hR⟩ := qr_unique (Q' := 1) (R' := 1) (transpose_mul_qrQ h) (by simp) (isUpperTriangular_qrR _) hup
    (qrR_diag_pos h) (fun j => by simp) (by rw [← eq_qrQ_mul_qrR h, Matrix.mul_one])
  exact ⟨hQ, hR⟩

/-- Concrete: the diagonal of a product of upper triangular `2 × 2` matrices. -/
example : (!![1, 2; 0, 3] * !![4, 5; 0, 6] : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 3 * 6 := by
  rw [diag_mul_of_isUpperTriangular]
  · simp
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all

/-- Boundary: with no columns (`k = 0`) the factorization is vacuous but still exists. -/
example (A : Matrix (Fin 3) (Fin 0) ℝ) :
    ∃ (Q : Matrix (Fin 3) (Fin 0) ℝ) (R : Matrix (Fin 0) (Fin 0) ℝ),
      Qᵀ * Q = 1 ∧ R.IsUpperTriangular ∧ (∀ j, 0 < R j j) ∧ A = Q * R :=
  exists_qr A (linearIndependent_empty_type)

/-- Uniqueness needs the positive diagonal: `(-I)(-I) = I · I` gives two factorizations of the
identity with orthonormal `Q` and upper triangular `R`. -/
example : (-1 : Matrix (Fin 2) (Fin 2) ℝ) * (-1) = 1 * 1 ∧
    (-1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ 1 := by
  refine ⟨by simp, fun h => ?_⟩
  have := congrFun (congrFun h 0) 0
  norm_num at this

end MathlibExtTest.LinearAlgebra.Matrix.QR
