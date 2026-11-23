/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity

@[expose] public section

open _root_.Matrix MathlibExt.LinearAlgebra.Matrix.SchurStrictPositivity

namespace MathlibExtTest.LinearAlgebra.Matrix.SchurStrictPositivity

/-- With an empty interior block the Schur complement is the exterior
block itself. -/
example : schurComplement (!![3] : Matrix (Fin 1) (Fin 1) ℝ)
    (0 : Matrix (Fin 1) (Fin 0) ℝ) (0 : Matrix (Fin 0) (Fin 0) ℝ)
    = !![3] :=
  schurComplement_eq_of_isEmpty _ _ _

/-- The scalar Schur complement through the public definition:
`2 - 1 * (1/1) * 1 = 1`. -/
example : schurComplement (!![2] : Matrix (Fin 1) (Fin 1) ℝ) !![1] !![1]
    = !![1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [schurComplement, Matrix.inv_def, Matrix.adjugate_fin_one,
      Matrix.mul_apply, dotProduct, Matrix.vecMul, Fin.sum_univ_one]

/-- A concrete positive-definite block matrix with decoupled blocks:
`G = [[2, 0], [0, 3]]` in block form. -/
private theorem posDef_diag_blocks :
    (Matrix.fromBlocks (!![2] : Matrix (Fin 1) (Fin 1) ℝ) 0 0
      (!![3] : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.IsHermitian]
  · intro x hx
    have hne : x (Sum.inl 0) ≠ 0 ∨ x (Sum.inr 0) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (by funext i; obtain (i | i) := i <;> fin_cases i <;> simp [h])
    have hpos : 0 < 2 * x (Sum.inl 0) ^ 2 + 3 * x (Sum.inr 0) ^ 2 := by
      rcases hne with h | h
      · have h1 : 0 < 2 * x (Sum.inl 0) ^ 2 := by positivity
        linarith [sq_nonneg (x (Sum.inr 0))]
      · have h1 : 0 < 3 * x (Sum.inr 0) ^ 2 := by positivity
        linarith [sq_nonneg (x (Sum.inl 0))]
    have heq : star x ⬝ᵥ (Matrix.fromBlocks (!![2] : Matrix (Fin 1) (Fin 1) ℝ)
          0 0 !![3]) *ᵥ x
        = 2 * x (Sum.inl 0) ^ 2 + 3 * x (Sum.inr 0) ^ 2 := by
      simp only [Matrix.fromBlocks_mulVec, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, Fin.sum_univ_one, Pi.star_apply, star_trivial,
        Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Matrix.transpose_zero,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      norm_num [Matrix.of_apply]
      ring
    rw [heq]
    exact hpos

/-- The interior block of the concrete matrix is positive definite,
through the public theorem. -/
example : (!![3] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  have h := interior_posDef (A := !![2]) (B := (0 : Matrix (Fin 1) (Fin 1) ℝ))
    (D := !![3]) posDef_diag_blocks
  simpa using h

/-- The Schur complement of the concrete matrix is positive definite,
through the public theorem: it is `!![2]`. -/
example : (schurComplement (!![2] : Matrix (Fin 1) (Fin 1) ℝ)
    (0 : Matrix (Fin 1) (Fin 1) ℝ) !![3]).PosDef :=
  schurComplement_posDef posDef_diag_blocks

/-- The scalar `Fin 1` specialization: `[[a, b], [b, d]]` positive
definite forces the scalar Schur complement positive. -/
example {a b d : ℝ}
    (hG : (Matrix.fromBlocks
      (Matrix.of fun _ _ => a : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => b : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => b : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => d : Matrix (Fin 1) (Fin 1) ℝ)).PosDef) :
    (schurComplement (Matrix.of fun _ _ => a : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => b : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.of fun _ _ => d : Matrix (Fin 1) (Fin 1) ℝ)).PosDef :=
  schurComplement_fin_one_posDef hG

end MathlibExtTest.LinearAlgebra.Matrix.SchurStrictPositivity
