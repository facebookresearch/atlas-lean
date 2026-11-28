/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Invertibility and inverses of `1 + A * B`

For rectangular matrices of opposite shapes, the Weinstein–Aronszajn identity
`Matrix.det_one_add_mul_comm` identifies the determinants of `1 + A * B` and `1 + B * A`.
Consequently these matrices are units simultaneously. The identity
`(1 + B * A) * B = B * (1 + A * B)` then gives an identity for their inverses; when the
determinants are not units, Mathlib's total matrix inverse sends both matrices to zero.
-/

public section

open Matrix

namespace MetaMathlibExt.Matrix

variable {m n R : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [CommRing R]

/-- The matrices `1 + A * B` and `1 + B * A` are invertible simultaneously, even if their
sizes differ. -/
theorem isUnit_one_add_mul_comm (A : Matrix m n R) (B : Matrix n m R) :
    IsUnit (1 + A * B) ↔ IsUnit (1 + B * A) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, Matrix.det_one_add_mul_comm]

/-- Multiplying by `B` after inverting `1 + A * B` is the same as multiplying by `B` before
inverting `1 + B * A`. No invertibility hypothesis is needed: if either determinant is not a
unit, both inverses are zero. -/
theorem mul_nonsing_inv_one_add_mul (A : Matrix m n R) (B : Matrix n m R) :
    B * (1 + A * B)⁻¹ = (1 + B * A)⁻¹ * B := by
  have hdet := Matrix.det_one_add_mul_comm A B
  by_cases hAB : IsUnit (1 + A * B).det
  · have hBA : IsUnit (1 + B * A).det := hdet ▸ hAB
    have hpush : (1 + B * A) * B = B * (1 + A * B) := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    calc
      B * (1 + A * B)⁻¹ = (1 + B * A)⁻¹ * ((1 + B * A) * (B * (1 + A * B)⁻¹)) :=
        (Matrix.nonsing_inv_mul_cancel_left _ _ hBA).symm
      _ = (1 + B * A)⁻¹ * B := by
        rw [← Matrix.mul_assoc (1 + B * A), hpush, Matrix.mul_nonsing_inv_cancel_right _ _ hAB]
  · have hBA : ¬IsUnit (1 + B * A).det := hdet ▸ hAB
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hAB, Matrix.nonsing_inv_apply_not_isUnit _ hBA,
      Matrix.mul_zero, Matrix.zero_mul]

end MetaMathlibExt.Matrix
