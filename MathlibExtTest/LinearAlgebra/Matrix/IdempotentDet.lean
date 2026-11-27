/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.IdempotentDet

@[expose] public section

namespace MatrixIdempotentDetTest

/-- Consumer with the original binders. -/
theorem exactSource {A : Type*} [CommRing A]
    {e : Matrix (Fin 2) (Fin 2) A} (he : IsIdempotentElem e) (htr : e.trace = 1) :
    e.det = 0 :=
  Matrix.det_eq_zero_of_isIdempotentElem_of_trace_eq_one he htr

/-- Without the trace hypothesis the conclusion fails: the identity matrix
is idempotent, has trace `2`, and has determinant `1 ≠ 0` over `ℤ`. -/
example : IsIdempotentElem (1 : Matrix (Fin 2) (Fin 2) ℤ) ∧
    (1 : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 ∧
    (1 : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  refine ⟨IsIdempotentElem.one, ?_, ?_⟩ <;> simp

/-- Without idempotence the conclusion fails: `!![2, 0; 0, -1]` has trace
`1` over `ℤ` but determinant `-2 ≠ 0`. -/
example : (!![2, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 ∧
    (!![2, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  constructor <;> simp [Matrix.trace_fin_two, Matrix.det_fin_two]

end MatrixIdempotentDetTest
