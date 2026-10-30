/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.FischerDeterminant

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for Fischer's determinant inequality

* `1 × 1` blocks `A = [2]`, `B = [1]`, `D = [3]`: `det [[A, B], [Bᵀ, D]] = 5 ≤ 6`,
  and the determinant equality fails (so the equality case of
  Fischer's inequality forces `B = 0`).
* `2 × 1` blocks `A = diag (2, 2)`, `B = (1, 0)ᵀ`, `D = [5]`:
  `det [[A, B], [Bᵀ, D]] = 18 ≤ 20`.
* Singular `A = diag (0, 2)` with `B = 0`: `det = 0 ≤ 0` (this
  exercises the `ε → 0⁺` perturbation in the proof).
* Determinant monotonicity: `det (diag ![1, 2]) = 2 ≤ 6 =
  det (diag ![2, 3])`.
* Eigenvalue bound: `W = diag ![2, 3]` has `W - 1` positive
  semidefinite and `det W = 6 ≥ 1`.
* Equality case with `B = 0`: `det [[A, 0], [0, D]] = det A * det D`.
-/

@[expose] public section

open scoped Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.FischerDeterminantTests

/-- `diagonal ![2]` is positive definite. -/
theorem posDef_diag_two : (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  rw [Matrix.posDef_diagonal_iff, Fin.forall_fin_one]
  norm_num [Matrix.cons_val_zero]

/-- `diagonal ![3]` is positive definite. -/
theorem posDef_diag_three :
    (Matrix.diagonal ![3] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  rw [Matrix.posDef_diagonal_iff, Fin.forall_fin_one]
  norm_num [Matrix.cons_val_zero]

/-- The Schur complement `3 - 1 * (1/2) * 1 = 5 / 2` is positive semidefinite. -/
theorem psd_schur_one_one :
    (Matrix.diagonal ![3] - (Matrix.diagonal ![1])ᴴ * (Matrix.diagonal ![2])⁻¹ *
      Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef := by
  have h1 : (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ)ᴴ = Matrix.diagonal ![1] := by
    ext i j
    fin_cases i; fin_cases j; simp [Matrix.diagonal]
  have h2 : (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ =
      Matrix.diagonal ![(2 : ℝ)⁻¹] := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i; fin_cases j
    norm_num [Matrix.mul_apply, Fin.sum_univ_one, Matrix.diagonal]
  rw [h1, h2, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
  intro i
  rw [Fin.eq_zero i]
  norm_num [Matrix.cons_val_zero, Pi.mul_apply, Pi.sub_apply]

/-- The `1 × 1` block matrix `[[2, 1], [1, 3]]` is positive semidefinite. -/
theorem psd_fromBlocks_one_one :
    (Matrix.fromBlocks (Matrix.diagonal ![2]) (Matrix.diagonal ![1])
      (Matrix.diagonal ![1])ᴴ (Matrix.diagonal ![3]) :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).PosSemidef := by
  have hInv : Invertible (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ) :=
    posDef_diag_two.isUnit.invertible
  exact (Matrix.PosDef.fromBlocks₁₁ _ _ posDef_diag_two).mpr psd_schur_one_one

/-- Determinant of the `1 × 1` block matrix: `det [[2, 1], [1, 3]] = 5`. -/
theorem det_fromBlocks_one_one :
    (Matrix.fromBlocks (Matrix.diagonal ![2]) (Matrix.diagonal ![1])
      (Matrix.diagonal ![1])ᴴ (Matrix.diagonal ![3]) :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).det = 5 := by
  have hsub : (Matrix.fromBlocks (Matrix.diagonal ![2]) (Matrix.diagonal ![1])
      (Matrix.diagonal ![1])ᴴ (Matrix.diagonal ![3])).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm = (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  calc (Matrix.fromBlocks (Matrix.diagonal ![2]) (Matrix.diagonal ![1])
        (Matrix.diagonal ![1])ᴴ (Matrix.diagonal ![3]) :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).det
      = ((Matrix.fromBlocks (Matrix.diagonal ![2]) (Matrix.diagonal ![1])
        (Matrix.diagonal ![1])ᴴ (Matrix.diagonal ![3])).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm).det :=
          (Matrix.det_submatrix_equiv_self finSumFinEquiv.symm _).symm
    _ = (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hsub]
    _ = 5 := by norm_num [Matrix.det_fin_two]

/-- Fischer's inequality on the `1 × 1` blocks: `5 ≤ 2 * 3`. -/
theorem fischer_one_one :
    (Matrix.fromBlocks (Matrix.diagonal ![2]) (Matrix.diagonal ![1])
      (Matrix.diagonal ![1])ᴴ (Matrix.diagonal ![3]) :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).det ≤ 6 := by
  calc (Matrix.fromBlocks (Matrix.diagonal ![2]) (Matrix.diagonal ![1])
        (Matrix.diagonal ![1])ᴴ (Matrix.diagonal ![3]) :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).det
      ≤ (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ).det *
          (Matrix.diagonal ![3] : Matrix (Fin 1) (Fin 1) ℝ).det :=
        Matrix.fischer_det_fromBlocks_le psd_fromBlocks_one_one
    _ = 6 := by norm_num [Matrix.det_diagonal, Fin.prod_univ_one]

/-- The determinant equality fails for the `1 × 1` example, since
`B = [1] ≠ 0`. -/
theorem fischer_one_one_det_ne :
    (Matrix.fromBlocks (Matrix.diagonal ![2]) (Matrix.diagonal ![1])
      (Matrix.diagonal ![1])ᴴ (Matrix.diagonal ![3]) :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).det ≠
      (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ).det *
        (Matrix.diagonal ![3] : Matrix (Fin 1) (Fin 1) ℝ).det := by
  rw [det_fromBlocks_one_one]
  norm_num [Matrix.det_diagonal, Fin.prod_univ_one]

/-- `diagonal ![2, 2]` is positive definite. -/
theorem posDef_diag_two_two :
    (Matrix.diagonal ![2, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  rw [Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The Schur complement `5 - (1, 0) * (1/2 • 1) * (1, 0)ᵀ = 9 / 2`
is positive semidefinite. -/
theorem psd_schur_two_one :
    (Matrix.diagonal ![5] - (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ *
      (Matrix.diagonal ![2, 2] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) :
      Matrix (Fin 1) (Fin 1) ℝ).PosSemidef := by
  have hprod : (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ *
      (Matrix.diagonal ![2, 2] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) =
      Matrix.diagonal ![(1 : ℝ) / 2] := by
    have hinv : (Matrix.diagonal ![2, 2] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
        Matrix.diagonal ![(2 : ℝ)⁻¹, (2 : ℝ)⁻¹] := by
      apply Matrix.inv_eq_left_inv
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.diagonal]
    rw [hinv]
    ext i j
    fin_cases i; fin_cases j
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.diagonal,
      Matrix.conjTranspose]
  rw [hprod, Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
  intro i
  rw [Fin.eq_zero i]
  norm_num [Matrix.cons_val_zero, Pi.sub_apply]

/-- The `2 × 1` block matrix is positive semidefinite. -/
theorem psd_fromBlocks_two_one :
    (Matrix.fromBlocks (Matrix.diagonal ![2, 2]) !![1; 0]
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ (Matrix.diagonal ![5]) :
      Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ).PosSemidef := by
  have hInv : Invertible (Matrix.diagonal ![2, 2] : Matrix (Fin 2) (Fin 2) ℝ) :=
    posDef_diag_two_two.isUnit.invertible
  exact (Matrix.PosDef.fromBlocks₁₁ _ _ posDef_diag_two_two).mpr psd_schur_two_one

/-- Determinant of the `2 × 1` block matrix:
`det [[2, 0, 1], [0, 2, 0], [1, 0, 5]] = 18`. -/
theorem det_fromBlocks_two_one :
    (Matrix.fromBlocks (Matrix.diagonal ![2, 2]) !![1; 0]
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ (Matrix.diagonal ![5]) :
      Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ).det = 18 := by
  have hsub : (Matrix.fromBlocks (Matrix.diagonal ![2, 2]) !![1; 0]
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ (Matrix.diagonal ![5])).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm =
      (!![2, 0, 1; 0, 2, 0; 1, 0, 5] : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  calc (Matrix.fromBlocks (Matrix.diagonal ![2, 2]) !![1; 0]
        (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ (Matrix.diagonal ![5]) :
        Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ).det
      = ((Matrix.fromBlocks (Matrix.diagonal ![2, 2]) !![1; 0]
        (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ (Matrix.diagonal ![5])).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm).det :=
          (Matrix.det_submatrix_equiv_self finSumFinEquiv.symm _).symm
    _ = (!![2, 0, 1; 0, 2, 0; 1, 0, 5] : Matrix (Fin 3) (Fin 3) ℝ).det := by rw [hsub]
    _ = 18 := by norm_num [Matrix.det_fin_three]

/-- Fischer's inequality on the `2 × 1` blocks: `18 ≤ 4 * 5`. -/
theorem fischer_two_one :
    (Matrix.fromBlocks (Matrix.diagonal ![2, 2]) !![1; 0]
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ (Matrix.diagonal ![5]) :
      Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ).det ≤ 20 := by
  calc (Matrix.fromBlocks (Matrix.diagonal ![2, 2]) !![1; 0]
        (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᴴ (Matrix.diagonal ![5]) :
        Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ).det
      ≤ (Matrix.diagonal ![2, 2] : Matrix (Fin 2) (Fin 2) ℝ).det *
          (Matrix.diagonal ![5] : Matrix (Fin 1) (Fin 1) ℝ).det :=
        Matrix.fischer_det_fromBlocks_le psd_fromBlocks_two_one
    _ = 20 := by
        norm_num [Matrix.det_diagonal, Fin.prod_univ_two, Fin.prod_univ_one]

/-- `diagonal ![0, 2]` is positive semidefinite (but singular). -/
theorem psd_diag_zero_two :
    (Matrix.diagonal ![0, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- The block-diagonal matrix with singular `A` is positive semidefinite. -/
theorem psd_fromBlocks_singular :
    (Matrix.fromBlocks (Matrix.diagonal ![0, 2]) (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ)ᴴ (Matrix.diagonal ![3, 4]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ).PosSemidef := by
  have hA : (Matrix.diagonal ![0, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef :=
    psd_diag_zero_two
  have hD : (Matrix.diagonal ![3, 4] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.fromBlocks hA.isHermitian rfl hD.isHermitian
  · intro x
    have ha := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have hd := hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    have hsplit : ∀ (u v : Fin 2 → ℝ),
        star x ⬝ᵥ Sum.elim u v =
          star (x ∘ Sum.inl) ⬝ᵥ u + star (x ∘ Sum.inr) ⬝ᵥ v := by
      intro u v
      simp [dotProduct, Fintype.sum_sum_type, Function.comp_apply, Pi.star_apply,
        Fin.sum_univ_two]
    rw [Matrix.fromBlocks_mulVec, hsplit]
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mulVec, add_zero, zero_add]
    exact add_nonneg ha hd

/-- Fischer's inequality with singular `A`: the conclusion `det ≤ det A * det D`
still holds (the proof goes through the `ε → 0⁺` perturbation). -/
theorem fischer_singular_le :
    (Matrix.fromBlocks (Matrix.diagonal ![0, 2]) (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ)ᴴ (Matrix.diagonal ![3, 4]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ).det ≤
      (Matrix.diagonal ![0, 2] : Matrix (Fin 2) (Fin 2) ℝ).det *
        (Matrix.diagonal ![3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det :=
  Matrix.fischer_det_fromBlocks_le psd_fromBlocks_singular

/-- Determinant of the singular block-diagonal matrix: `det = 0`. -/
theorem det_fromBlocks_singular :
    (Matrix.fromBlocks (Matrix.diagonal ![0, 2]) (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ)ᴴ (Matrix.diagonal ![3, 4]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ).det = 0 := by
  calc (Matrix.fromBlocks (Matrix.diagonal ![0, 2]) (0 : Matrix (Fin 2) (Fin 2) ℝ)
        (0 : Matrix (Fin 2) (Fin 2) ℝ)ᴴ (Matrix.diagonal ![3, 4]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ).det
      = (Matrix.diagonal ![0, 2] : Matrix (Fin 2) (Fin 2) ℝ).det *
          (Matrix.diagonal ![3, 4] : Matrix (Fin 2) (Fin 2) ℝ).det := by
        rw [show (0 : Matrix (Fin 2) (Fin 2) ℝ)ᴴ = 0 by simp]
        exact Matrix.det_fromBlocks_zero₁₂ _ _ _
    _ = 0 := by norm_num [Matrix.det_diagonal, Fin.prod_univ_two]

/-- Determinant monotonicity: `det (diag ![1, 2]) = 2 ≤ 6 =
det (diag ![2, 3])`. -/
theorem det_le_det_diag :
    (2 : ℝ) ≤ (Matrix.diagonal ![2, 3] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  have hS : (Matrix.diagonal ![1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hSD : (Matrix.diagonal ![2, 3] - Matrix.diagonal ![1, 2] :
      Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
    rw [Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  calc (2 : ℝ) = (Matrix.diagonal ![1, 2] : Matrix (Fin 2) (Fin 2) ℝ).det := by
        norm_num [Matrix.det_diagonal, Fin.prod_univ_two]
    _ ≤ (Matrix.diagonal ![2, 3] : Matrix (Fin 2) (Fin 2) ℝ).det :=
        Matrix.det_le_det_of_posSemidef_le hS hSD

/-- Eigenvalue bound: `1 ≤ det (diag ![2, 3]) = 6`. -/
theorem one_le_det_diag :
    1 ≤ (Matrix.diagonal ![2, 3] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  have hW : (Matrix.diagonal ![2, 3] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have h : (Matrix.diagonal ![2, 3] - 1 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
    have h1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
    rw [h1, Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> simp
  exact Matrix.one_le_det_of_posSemidef_sub_one hW h

/-- Equality case with `B = 0`: `det [[A, 0], [0, D]] = det A * det D`. -/
theorem fischer_eq_zero_block :
    (Matrix.fromBlocks (Matrix.diagonal ![2]) (0 : Matrix (Fin 1) (Fin 1) ℝ)
      (0 : Matrix (Fin 1) (Fin 1) ℝ)ᴴ (Matrix.diagonal ![3]) :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).det =
      (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ).det *
        (Matrix.diagonal ![3] : Matrix (Fin 1) (Fin 1) ℝ).det := by
  have hM : (Matrix.fromBlocks (Matrix.diagonal ![2]) (0 : Matrix (Fin 1) (Fin 1) ℝ)
      (0 : Matrix (Fin 1) (Fin 1) ℝ)ᴴ (Matrix.diagonal ![3]) :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).PosSemidef := by
    have hInv : Invertible (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ) :=
      posDef_diag_two.isUnit.invertible
    have hS : (Matrix.diagonal ![3] - (0 : Matrix (Fin 1) (Fin 1) ℝ)ᴴ *
        (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * 0 :
        Matrix (Fin 1) (Fin 1) ℝ).PosSemidef := by
      simp
    exact (Matrix.PosDef.fromBlocks₁₁ _ _ posDef_diag_two).mpr hS
  exact (Matrix.fischer_det_fromBlocks_eq_iff posDef_diag_two posDef_diag_three hM).mpr rfl

end MathlibExtTest.LinearAlgebra.Matrix.FischerDeterminantTests
