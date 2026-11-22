/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Analysis.Matrix.NormalSpectralTheorem
import Mathlib.Tactic

namespace MathlibExtTest.Analysis.Matrix.NormalSpectralTheorem

/-- The real `90°` rotation matrix, a non-Hermitian normal matrix. -/
private def rotation : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- A complex diagonal matrix: normal, with the non-real eigenvalue `Complex.I`. -/
private def complexDiagonal : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, Complex.I]

/-- The `2 × 2` nilpotent Jordan block, which is not normal. -/
private def nilpotent : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

private lemma rotation_isStarNormal : IsStarNormal rotation := by
  refine ⟨?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private lemma complexDiagonal_isStarNormal : IsStarNormal complexDiagonal := by
  refine ⟨?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiagonal, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]

private lemma nilpotent_not_isStarNormal : ¬ IsStarNormal nilpotent := by
  intro h
  have h00 := congr_fun (congr_fun h.star_comm_self 0) 0
  simp [nilpotent, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at h00

/-- The rotation matrix is unitarily diagonalizable. -/
example : ∃ (P : Matrix (Fin 2) (Fin 2) ℂ) (_ : P ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (d : Fin 2 → ℂ), star P * rotation * P = Matrix.diagonal d :=
  Matrix.exists_unitary_diagonal_of_isStarNormal rotation_isStarNormal

/-- The complex diagonal matrix is unitarily diagonalizable. -/
example : ∃ (P : Matrix (Fin 2) (Fin 2) ℂ) (_ : P ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (d : Fin 2 → ℂ), star P * complexDiagonal * P = Matrix.diagonal d :=
  Matrix.exists_unitary_diagonal_of_isStarNormal complexDiagonal_isStarNormal

/-- The diagonalizing matrix can be chosen unitary: `star P * P = 1`. -/
example : ∃ (P : Matrix (Fin 2) (Fin 2) ℂ) (_ : P ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (d : Fin 2 → ℂ), star P * P = 1 ∧ star P * rotation * P = Matrix.diagonal d := by
  obtain ⟨P, hP, d, hd⟩ :=
    Matrix.exists_unitary_diagonal_of_isStarNormal rotation_isStarNormal
  exact ⟨P, hP, d, Matrix.mem_unitaryGroup_iff'.mp hP, hd⟩

/-- Normality is a genuine hypothesis: the nilpotent Jordan block is not normal. -/
example : ¬ IsStarNormal nilpotent := nilpotent_not_isStarNormal

end MathlibExtTest.Analysis.Matrix.NormalSpectralTheorem
