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

/-- The diagonal matrix `diag(s, s⁻¹)` has eigenvalues `s` and `s⁻¹`. -/
theorem diag_hasEigenvalues {F : Type*} [Field F] (s : F) (hs : s ≠ 0) :
    HasEigenvalues (Matrix.SpecialLinearGroup.diag2 s hs) s := by
  unfold HasEigenvalues
  rw [Matrix.SpecialLinearGroup.diag2_coe, Matrix.charpoly_diagonal,
    Fin.prod_univ_two]

/-- The standard diagonal element is conjugate to itself. -/
theorem diag_isConj {F : Type*} [Field F] (s : F) (hs : s ≠ 0) :
    IsConj (Matrix.SpecialLinearGroup.diag2 s hs)
      (Matrix.SpecialLinearGroup.diag2 s hs) := IsConj.refl _

/-- The swap matrix in `SL₂(ℚ)`. -/
private def swapSL2 : Matrix.SpecialLinearGroup (Fin 2) ℚ :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- Conjugating `diag(2, 2⁻¹)` by the swap matrix gives a matrix with
eigenvalues `2` and `2⁻¹`: the characteristic polynomial is invariant under
conjugation (here via `charpoly_mul_comm` and `adjugate_mul`, since the
inverse in `SL₂` is the adjugate). -/
theorem conj_diag_hasEigenvalues :
    HasEigenvalues
      (swapSL2 * Matrix.SpecialLinearGroup.diag2 (2 : ℚ) (by norm_num) *
        swapSL2⁻¹) 2 := by
  have hdet : (swapSL2 : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := swapSL2.2
  have hcoe_diag : ((Matrix.SpecialLinearGroup.diag2 (2 : ℚ) (by norm_num) :
      Matrix.SpecialLinearGroup (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal ![2, (2 : ℚ)⁻¹] := by
    rw [Matrix.SpecialLinearGroup.diag2_coe']
    ext i j
    fin_cases i <;> fin_cases j <;> simp
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
theorem conj_diag_isConj :
    IsConj
      (swapSL2 * Matrix.SpecialLinearGroup.diag2 (2 : ℚ) (by norm_num) *
        swapSL2⁻¹)
      (Matrix.SpecialLinearGroup.diag2 (2 : ℚ) (by norm_num)) :=
  eigenvalues_implies_isConj_diag2 2 (by norm_num) _ conj_diag_hasEigenvalues
    (by norm_num)

/-- If a normal subgroup of `SL₂(ℚ)` contains `diag(2, 2⁻¹)`, it also contains
the conjugate of `diag(2, 2⁻¹)` by the swap matrix. -/
theorem conj_diag_mem_of_mem
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℚ)) (hN : N.Normal)
    (hB : Matrix.SpecialLinearGroup.diag2 (2 : ℚ) (by norm_num) ∈ N) :
    swapSL2 * Matrix.SpecialLinearGroup.diag2 (2 : ℚ) (by norm_num) *
      swapSL2⁻¹ ∈ N :=
  normal_contains_all_with_eigenvalues N hN 2 (by norm_num) _ hB
    (diag_hasEigenvalues 2 (by norm_num)) _ conj_diag_hasEigenvalues

/-- A nontrivial matrix with repeated eigenvalues `1` and `1`. -/
private def unipotent : Matrix.SpecialLinearGroup (Fin 2) ℚ :=
  ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two]⟩

/-- The source predicate includes matrices with repeated eigenvalues. -/
theorem unipotent_hasEigenvalues_one : HasEigenvalues unipotent 1 := by
  unfold HasEigenvalues
  rw [Matrix.charpoly_fin_two]
  norm_num [unipotent, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two,
    Polynomial.C_ofNat]
  ring

/-- Repeated eigenvalues do not imply conjugacy to the identity. -/
theorem unipotent_not_isConj_one : ¬ IsConj unipotent 1 := by
  rw [isConj_one_left]
  intro h
  have h01 := congrArg
    (fun M : Matrix.SpecialLinearGroup (Fin 2) ℚ => M.1 0 1) h
  norm_num [unipotent] at h01

/-- The source theorem gives an actual member of a concrete normal closure. -/
theorem conj_diag_mem_normalClosure :
    swapSL2 * Matrix.SpecialLinearGroup.diag2 (2 : ℚ) (by norm_num) *
      swapSL2⁻¹ ∈
      Subgroup.normalClosure
        ({Matrix.SpecialLinearGroup.diag2 (2 : ℚ) (by norm_num)} :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℚ)) :=
  conj_diag_mem_of_mem _ inferInstance (Subgroup.subset_normalClosure (by simp))

/-- Negative reciprocal eigenvalues use the same canonical diagonalization API. -/
theorem negative_diagonal_isConj :
    IsConj (Matrix.SpecialLinearGroup.diag2 (-2 : ℚ) (by norm_num))
      (Matrix.SpecialLinearGroup.diag2 (-2 : ℚ) (by norm_num)) :=
  eigenvalues_implies_isConj_diag2 (-2) (by norm_num) _
    (diag_hasEigenvalues (-2) (by norm_num)) (by norm_num)

/-- The diagonal and its concrete swapped conjugate use standard symmetry. -/
theorem diag_isConj_swapped :
    IsConj (Matrix.SpecialLinearGroup.diag2 (2 : ℚ) (by norm_num))
      (swapSL2 * Matrix.SpecialLinearGroup.diag2 (2 : ℚ) (by norm_num) *
        swapSL2⁻¹) := conj_diag_isConj.symm

/-- The repeated-eigenvalue example is not conjugate to the standard diagonal. -/
theorem unipotent_not_isConj_diag2 :
    ¬ IsConj unipotent (Matrix.SpecialLinearGroup.diag2 (1 : ℚ) (by norm_num)) := by
  have hdiag : Matrix.SpecialLinearGroup.diag2 (1 : ℚ) (by norm_num) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.diag2_coe']
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  simpa [hdiag] using unipotent_not_isConj_one

#print axioms diag_hasEigenvalues
#print axioms diag_isConj
#print axioms conj_diag_hasEigenvalues
#print axioms conj_diag_isConj
#print axioms conj_diag_mem_of_mem
#print axioms unipotent_hasEigenvalues_one
#print axioms unipotent_not_isConj_one
#print axioms conj_diag_mem_normalClosure
#print axioms negative_diagonal_isConj
#print axioms diag_isConj_swapped
#print axioms unipotent_not_isConj_diag2

end MathlibExtTest.GroupTheory.SL2EigenvalueConjugacy
