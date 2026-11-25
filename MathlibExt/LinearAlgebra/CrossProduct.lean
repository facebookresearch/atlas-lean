/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Cross products under a real `3 × 3` matrix

A real `3 × 3` matrix `Q` maps cross products through its cofactor matrix,
`(Q a) ⨯₃ (Q b) = (adjugate Q)ᵀ (a ⨯₃ b)`. For orthogonal `Q` the cofactor matrix is
`det Q • Q`, so `(Q a) ⨯₃ (Q b) = det Q • Q (a ⨯₃ b)`: a rotation preserves cross products and
a reflection of determinant `-1` reverses them.

## Main results

- `Matrix.mulVec_cross_mulVec` : the cofactor law.
- `Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup` : the orthogonal case.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

/-- The cross product transforms with the cofactor matrix: `(Q a) ⨯₃ (Q b) = (adj Q)ᵀ (a ⨯₃ b)`. -/
lemma mulVec_cross_mulVec (Q : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    (Q *ᵥ a) ⨯₃ (Q *ᵥ b) = (adjugate Q)ᵀ *ᵥ (a ⨯₃ b) := by
  ext i
  fin_cases i <;>
  · simp [cross_apply, adjugate_fin_three, mulVec, dotProduct, Fin.sum_univ_three]
    ring

/-- An orthogonal matrix `Q` maps cross products to `det Q •` cross products. -/
lemma mulVec_cross_mulVec_of_mem_orthogonalGroup {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (a b : Fin 3 → ℝ) :
    (Q *ᵥ a) ⨯₃ (Q *ᵥ b) = Q.det • (Q *ᵥ (a ⨯₃ b)) := by
  have h2 : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hQ
  have hadj : adjugate Q = Q.det • Qᵀ := by
    calc adjugate Q = Qᵀ * Q * adjugate Q := by rw [h2, Matrix.one_mul]
      _ = Qᵀ * (Q.det • 1) := by rw [Matrix.mul_assoc, mul_adjugate]
      _ = Q.det • Qᵀ := by rw [Matrix.mul_smul, Matrix.mul_one]
  rw [mulVec_cross_mulVec, hadj, transpose_smul, transpose_transpose, smul_mulVec]

end Matrix
