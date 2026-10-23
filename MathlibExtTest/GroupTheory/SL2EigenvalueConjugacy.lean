/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SL2EigenvalueConjugacy

import Mathlib.Tactic

namespace MathlibExtTest.GroupTheory.SL2EigenvalueConjugacy

open _root_.SL2

/-- The diagonal matrix `diag(s, s⁻¹)` in `SL₂(F)`. -/
private def diagSL2 {F : Type*} [Field F] (s : F) (hs : s ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨Matrix.diagonal ![s, s⁻¹], by
    simp only [Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact mul_inv_cancel₀ hs⟩

/-- The diagonal matrix `diag(s, s⁻¹)` has eigenvalues `s` and `s⁻¹`. -/
theorem diag_hasEigenvalues {F : Type*} [Field F] (s : F) (hs : s ≠ 0) :
    HasEigenvalues (diagSL2 s hs) s := by
  unfold HasEigenvalues
  have hcoe : ((diagSL2 s hs : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![s, s⁻¹] := rfl
  rw [hcoe, Matrix.charpoly_diagonal, Fin.prod_univ_two]
  simp

/-- The diagonal matrix `diag(s, s⁻¹)` is conjugate to itself. -/
theorem diag_isConjToDiag {F : Type*} [Field F] (s : F) (hs : s ≠ 0) :
    IsConjToDiag (diagSL2 s hs) s := by
  refine ⟨1, ?_⟩
  rw [inv_one, mul_one, one_mul]
  rfl

/-- The swap matrix in `SL₂(ℚ)`. -/
private def swapSL2 : Matrix.SpecialLinearGroup (Fin 2) ℚ :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- Conjugating `diag(2, 2⁻¹)` by the swap matrix gives a matrix with
eigenvalues `2` and `2⁻¹`: the characteristic polynomial is invariant under
conjugation (here via `charpoly_mul_comm` and `adjugate_mul`, since the
inverse in `SL₂` is the adjugate). -/
theorem conj_diag_hasEigenvalues :
    HasEigenvalues (swapSL2 * diagSL2 (2 : ℚ) (by norm_num) * swapSL2⁻¹) 2 := by
  have hdet : (swapSL2 : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := swapSL2.2
  have hcoe_diag : ((diagSL2 (2 : ℚ) (by norm_num) :
      Matrix.SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal ![2, (2 : ℚ)⁻¹] := rfl
  unfold HasEigenvalues
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    hcoe_diag]
  calc ((swapSL2 : Matrix (Fin 2) (Fin 2) ℚ) * Matrix.diagonal ![2, (2 : ℚ)⁻¹] *
        Matrix.adjugate (swapSL2 : Matrix (Fin 2) (Fin 2) ℚ)).charpoly
      = ((Matrix.adjugate (swapSL2 : Matrix (Fin 2) (Fin 2) ℚ)) *
          ((swapSL2 : Matrix (Fin 2) (Fin 2) ℚ) * Matrix.diagonal ![2, (2 : ℚ)⁻¹])).charpoly :=
        Matrix.charpoly_mul_comm _ _
    _ = (((Matrix.adjugate (swapSL2 : Matrix (Fin 2) (Fin 2) ℚ)) *
          (swapSL2 : Matrix (Fin 2) (Fin 2) ℚ)) * Matrix.diagonal ![2, (2 : ℚ)⁻¹]).charpoly := by
        rw [Matrix.mul_assoc]
    _ = (Matrix.diagonal ![2, (2 : ℚ)⁻¹]).charpoly := by
        rw [Matrix.adjugate_mul, hdet, one_smul, Matrix.one_mul]
    _ = (Polynomial.X - Polynomial.C 2) * (Polynomial.X - Polynomial.C (2 : ℚ)⁻¹) := by
        rw [Matrix.charpoly_diagonal, Fin.prod_univ_two]; simp

/-- The conjugate of `diag(2, 2⁻¹)` by the swap matrix is conjugate to
`diag(2, 2⁻¹)`, by the diagonalization theorem. -/
theorem conj_diag_isConjToDiag :
    IsConjToDiag (swapSL2 * diagSL2 (2 : ℚ) (by norm_num) * swapSL2⁻¹) 2 :=
  eigenvalues_implies_conj_to_diag 2 (by norm_num) _ conj_diag_hasEigenvalues

/-- If a normal subgroup of `SL₂(ℚ)` contains `diag(2, 2⁻¹)`, it also contains
the conjugate of `diag(2, 2⁻¹)` by the swap matrix. -/
theorem conj_diag_mem_of_mem
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℚ)) (hN : N.Normal)
    (hB : diagSL2 (2 : ℚ) (by norm_num) ∈ N) :
    swapSL2 * diagSL2 (2 : ℚ) (by norm_num) * swapSL2⁻¹ ∈ N :=
  normal_contains_all_with_eigenvalues N hN 2 (by norm_num) _ hB
    (diag_hasEigenvalues 2 (by norm_num)) _ conj_diag_hasEigenvalues

end MathlibExtTest.GroupTheory.SL2EigenvalueConjugacy
