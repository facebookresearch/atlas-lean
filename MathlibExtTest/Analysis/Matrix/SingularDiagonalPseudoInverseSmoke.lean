/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.Matrix.HermitianPseudoInverse
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Spectral reciprocal and support of a singular diagonal matrix

The Hermitian complex matrix `diag(2,0)` has spectral pseudoinverse
`diag(1/2,0)` and support `diag(1,0)`. Both values are computed from the
actual real continuous functional calculus on the spectrum. The support
preserves the first coordinate and annihilates the second, and the computed
pseudoinverse satisfies all four Moore–Penrose equations. The empty matrix
case retains the total zero convention.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace MathlibExtTest.SingularDiagonalPseudoInverse

private def singularDiagonal : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 2 else 0)

private def supportDiagonal : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else 0)

private def inverseDiagonal : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 1 / 2 else 0)

private theorem singular_hermitian : singularDiagonal.IsHermitian := by
  change singularDiagonalᴴ = singularDiagonal
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [singularDiagonal, Matrix.conjTranspose_apply]

private theorem support_hermitian : supportDiagonal.IsHermitian := by
  change supportDiagonalᴴ = supportDiagonal
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [supportDiagonal, Matrix.conjTranspose_apply]

private theorem support_idempotent : IsIdempotentElem supportDiagonal := by
  change supportDiagonal * supportDiagonal = supportDiagonal
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [supportDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

private theorem scaled_support :
    cfc (fun x : ℝ => 2 * x) supportDiagonal = singularDiagonal := by
  rw [cfc_const_mul_id (2 : ℝ) supportDiagonal support_hermitian.isSelfAdjoint]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [singularDiagonal, supportDiagonal]

private theorem singular_spectrum_subset :
    spectrum ℝ singularDiagonal ⊆ ({0, 2} : Set ℝ) := by
  have hp : spectrum ℝ supportDiagonal ⊆ ({0, 1} : Set ℝ) :=
    (isIdempotentElem_iff_spectrum_subset ℝ supportDiagonal
      support_hermitian.isSelfAdjoint).mp support_idempotent
  have hs : spectrum ℝ singularDiagonal =
      (fun x : ℝ => 2 * x) '' spectrum ℝ supportDiagonal := by
    rw [← scaled_support]
    exact cfc_map_spectrum (fun x : ℝ => 2 * x) supportDiagonal
      support_hermitian.isSelfAdjoint (continuous_const.mul continuous_id).continuousOn
  intro x hx
  rw [hs] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y = 0 ∨ y = 1 := by simpa using hp hy
  rcases hy' with rfl | rfl <;> simp

private theorem inverse_computation :
    Matrix.spectralPseudoInverse singularDiagonal = inverseDiagonal := by
  unfold Matrix.spectralPseudoInverse
  calc
    cfc (fun x : ℝ => x⁻¹) singularDiagonal =
        cfc (fun x : ℝ => (1 / 4) * x) singularDiagonal := by
      apply cfc_congr
      intro x hx
      have hx' : x = 0 ∨ x = 2 := by simpa using singular_spectrum_subset hx
      rcases hx' with rfl | rfl <;> norm_num
    _ = (1 / 4 : ℝ) • singularDiagonal :=
      cfc_const_mul_id (1 / 4 : ℝ) singularDiagonal singular_hermitian.isSelfAdjoint
    _ = inverseDiagonal := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [singularDiagonal, inverseDiagonal]

private theorem support_computation :
    Matrix.spectralSupport singularDiagonal = supportDiagonal := by
  unfold Matrix.spectralSupport
  calc
    cfc (fun x : ℝ => if x = 0 then 0 else 1) singularDiagonal =
        cfc (fun x : ℝ => (1 / 2) * x) singularDiagonal := by
      apply cfc_congr
      intro x hx
      have hx' : x = 0 ∨ x = 2 := by simpa using singular_spectrum_subset hx
      rcases hx' with rfl | rfl <;> norm_num
    _ = (1 / 2 : ℝ) • singularDiagonal :=
      cfc_const_mul_id (1 / 2 : ℝ) singularDiagonal singular_hermitian.isSelfAdjoint
    _ = supportDiagonal := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [singularDiagonal, supportDiagonal]

example : singularDiagonal.IsHermitian ∧ singularDiagonal ≠ 0 ∧ singularDiagonal.det = 0 := by
  refine ⟨singular_hermitian, ?_, ?_⟩
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    norm_num [singularDiagonal] at h00
  · norm_num [singularDiagonal, Matrix.det_fin_two]

example :
    Matrix.spectralPseudoInverse singularDiagonal = inverseDiagonal ∧
      (Matrix.spectralPseudoInverse singularDiagonal) 0 0 = 1 / 2 ∧
      (Matrix.spectralPseudoInverse singularDiagonal) 1 1 = 0 := by
  rw [inverse_computation]
  norm_num [inverseDiagonal]

example :
    Matrix.spectralSupport singularDiagonal = supportDiagonal ∧
      Matrix.spectralSupport singularDiagonal ≠ 0 ∧
      Matrix.spectralSupport singularDiagonal ≠ 1 := by
  rw [support_computation]
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    norm_num [supportDiagonal] at h00
  · intro h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
    norm_num [supportDiagonal] at h11

example :
    singularDiagonal * Matrix.spectralPseudoInverse singularDiagonal * singularDiagonal =
        singularDiagonal ∧
      Matrix.spectralPseudoInverse singularDiagonal * singularDiagonal *
        Matrix.spectralPseudoInverse singularDiagonal =
        Matrix.spectralPseudoInverse singularDiagonal ∧
      (singularDiagonal * Matrix.spectralPseudoInverse singularDiagonal)ᴴ =
        singularDiagonal * Matrix.spectralPseudoInverse singularDiagonal ∧
      (Matrix.spectralPseudoInverse singularDiagonal * singularDiagonal)ᴴ =
        Matrix.spectralPseudoInverse singularDiagonal * singularDiagonal :=
  singular_hermitian.spectralPseudoInverse_penrose

example :
    Matrix.spectralSupport singularDiagonal *ᵥ (fun i : Fin 2 => if i = 0 then Complex.I else 0) =
        (fun i : Fin 2 => if i = 0 then Complex.I else 0) ∧
      Matrix.spectralSupport singularDiagonal *ᵥ (fun i : Fin 2 => if i = 1 then Complex.I else 0) =
        0 := by
  rw [support_computation]
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [supportDiagonal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example :
    Matrix.spectralPseudoInverse (0 : Matrix (Fin 0) (Fin 0) ℂ) = 0 ∧
      Matrix.spectralSupport (0 : Matrix (Fin 0) (Fin 0) ℂ) = 0 := by
  simp

end MathlibExtTest.SingularDiagonalPseudoInverse
