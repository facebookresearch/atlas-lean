/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Normal subgroups of `SL₂` contain all matrices with given eigenvalues

If a normal subgroup `N` of `SL₂(F)` contains one matrix whose characteristic
polynomial is `(X - s)(X - s⁻¹)` with `s ≠ s⁻¹`, then `N` contains every
matrix with those eigenvalues. The reason is conjugacy: such a matrix is
conjugate in `SL₂(F)` to the diagonal matrix `diag(s, s⁻¹)`, so any two
matrices with the same eigenvalues are conjugate to each other, and a normal
subgroup is closed under conjugation.

Source: `v1/Atlas/AlgebraNotes/code/SimpleGroups.lean` (the `SL2`
definitions and the three `sl2_*` theorems; the rest of that file, including
the `SU₂` simplicity material and the unproved `det_exp`, is not ported).
-/

@[expose] public section

namespace SL2

variable {F : Type*} [Field F]

/-- A matrix `M` in `SL₂(F)` has eigenvalues `s` and `s⁻¹` if its
characteristic polynomial is `(X - s)(X - s⁻¹)`. -/
def HasEigenvalues (M : Matrix.SpecialLinearGroup (Fin 2) F) (s : F) : Prop :=
  (↑M : Matrix (Fin 2) (Fin 2) F).charpoly =
    (Polynomial.X - Polynomial.C s) * (Polynomial.X - Polynomial.C s⁻¹)

/-- Conjugacy to `Matrix.SpecialLinearGroup.diag2` is equivalent to the source
statement about a matrix conjugator. -/
theorem isConj_diag2_iff (M : Matrix.SpecialLinearGroup (Fin 2) F)
    (s : F) (hs0 : s ≠ 0) :
    IsConj M (Matrix.SpecialLinearGroup.diag2 s hs0) ↔
      ∃ P : Matrix.SpecialLinearGroup (Fin 2) F,
        (P * M * P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 =
          Matrix.diagonal ![s, s⁻¹] := by
  have hdiag : (Matrix.SpecialLinearGroup.diag2 s hs0).1 =
      Matrix.diagonal ![s, s⁻¹] := by
    rw [Matrix.SpecialLinearGroup.diag2_coe']
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [isConj_iff]
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨P, ?_⟩
    rw [hP]
    exact hdiag
  · rintro ⟨P, hP⟩
    refine ⟨P, ?_⟩
    exact Subtype.ext (hP.trans hdiag.symm)

/-- A normal subgroup of `SL₂(F)` containing one matrix conjugate to
`diag(s, s⁻¹)` contains every matrix conjugate to `diag(s, s⁻¹)`: the two
matrices are conjugate to each other, via the diagonal matrix, and a normal
subgroup is closed under conjugation. -/
theorem normal_subgroup_contains_all_conj_to_diag
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hN : N.Normal) (s : F)
    (B : Matrix.SpecialLinearGroup (Fin 2) F) (hB : B ∈ N)
    (hBdiag : ∃ P : Matrix.SpecialLinearGroup (Fin 2) F,
      (P * B * P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 =
        Matrix.diagonal ![s, s⁻¹])
    (Q : Matrix.SpecialLinearGroup (Fin 2) F)
    (hQdiag : ∃ P : Matrix.SpecialLinearGroup (Fin 2) F,
      (P * Q * P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 =
        Matrix.diagonal ![s, s⁻¹]) :
    Q ∈ N := by
  obtain ⟨PB, hPB⟩ := hBdiag
  obtain ⟨PQ, hPQ⟩ := hQdiag
  have hcommon : PB * B * PB⁻¹ = PQ * Q * PQ⁻¹ :=
    Subtype.ext (hPB.trans hPQ.symm)
  have hBconj : IsConj B (PB * B * PB⁻¹) := isConj_iff.mpr ⟨PB, rfl⟩
  have hQconj : IsConj Q (PB * B * PB⁻¹) := isConj_iff.mpr ⟨PQ, hcommon.symm⟩
  obtain ⟨P, hP⟩ := isConj_iff.mp (hBconj.trans hQconj.symm)
  rw [← hP]
  exact hN.conj_mem B hB P

open Polynomial Module.End in
set_option maxHeartbeats 8000000 in
/-- A matrix in `SL₂(F)` whose eigenvalues are `s` and `s⁻¹`, with `s ≠ s⁻¹`,
is conjugate in `SL₂(F)` to `diag(s, s⁻¹)`. The proof builds the conjugating
matrix from eigenvectors for `s` and `s⁻¹`: distinct eigenvalues give
linearly independent eigenvectors, so the matrix of eigenvectors has
nonzero determinant, and rescaling its first column makes the determinant `1`. -/
theorem eigenvalues_implies_isConj_diag2 (s : F) (hs : s ≠ s⁻¹)
    (M : Matrix.SpecialLinearGroup (Fin 2) F) (hM : HasEigenvalues M s)
    (hs0 : s ≠ 0) : IsConj M (Matrix.SpecialLinearGroup.diag2 s hs0) := by
  open Polynomial Module.End in
  unfold HasEigenvalues at hM
  apply (isConj_diag2_iff M s hs0).mpr
  have hs_sub : s - s⁻¹ ≠ 0 := sub_ne_zero.mpr hs
  set M' := (↑M : Matrix (Fin 2) (Fin 2) F)
  have heig_s : HasEigenvalue (Matrix.toLin' M') s := by
    rw [hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM]; simp [IsRoot]
  have heig_sinv : HasEigenvalue (Matrix.toLin' M') s⁻¹ := by
    rw [hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM]; simp [IsRoot]
  obtain ⟨v₁, hv₁_mem, hv₁_ne⟩ := (Submodule.ne_bot_iff _).mp (hasEigenvalue_iff.mp heig_s)
  obtain ⟨v₂, hv₂_mem, hv₂_ne⟩ := (Submodule.ne_bot_iff _).mp (hasEigenvalue_iff.mp heig_sinv)
  rw [mem_eigenspace_iff] at hv₁_mem hv₂_mem
  have hd : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0 := by
    intro hd0
    have hd_eq : v₁ 0 * v₂ 1 = v₁ 1 * v₂ 0 := sub_eq_zero.mp hd0
    have hprop : ∃ a : F, v₁ = a • v₂ := by
      by_cases hv20 : v₂ 0 = 0
      · have hv21 : v₂ 1 ≠ 0 := fun h21 => hv₂_ne (funext fun i => by fin_cases i <;> assumption)
        have hv10 : v₁ 0 = 0 := by
          have h := hd_eq; rw [hv20, mul_zero] at h; exact (mul_eq_zero.mp h).resolve_right hv21
        exact ⟨v₁ 1 / v₂ 1, funext fun i => by
          fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hv10, hv20, div_mul_cancel₀ _ hv21]⟩
      · exact ⟨v₁ 0 / v₂ 0, funext fun i => by
          fin_cases i
          · simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hv20]
          · simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
            rw [eq_div_iff hv20]
            have h1 : (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) := rfl
            simp only [h1]; ring_nf
            simp only [show v₁ 1 * v₂ 0 = v₁ 0 * v₂ 1 from hd_eq.symm]⟩
    obtain ⟨a, ha⟩ := hprop
    have h1 := hv₁_mem; rw [ha, map_smul, hv₂_mem, smul_smul, smul_smul] at h1
    have heq2 : a * s⁻¹ = s * a := smul_left_injective _ hv₂_ne h1
    have h4 : a * (s - s⁻¹) = 0 := by linear_combination (mul_comm s a).symm.trans heq2.symm
    rcases mul_eq_zero.mp h4 with h | h
    · rw [h, zero_smul] at ha; exact hv₁_ne ha
    · exact hs_sub h
  set d := v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0
  let Q_mat : Matrix (Fin 2) (Fin 2) F :=
    Matrix.of fun i j => if j = (0 : Fin 2) then d⁻¹ * v₁ i else v₂ i
  have hQ_det : Q_mat.det = 1 := by
    simp only [Q_mat, Matrix.det_fin_two, Matrix.of_apply]; norm_num; field_simp; ring
  let Q : Matrix.SpecialLinearGroup (Fin 2) F := ⟨Q_mat, hQ_det⟩
  have hv₁_eq : ∀ i, M' i 0 * v₁ 0 + M' i 1 * v₁ 1 = s * v₁ i := fun i => by
    have := congr_fun hv₁_mem i
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, smul_eq_mul,
      Fin.sum_univ_two] using this
  have hv₂_eq : ∀ i, M' i 0 * v₂ 0 + M' i 1 * v₂ 1 = s⁻¹ * v₂ i := fun i => by
    have := congr_fun hv₂_mem i
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, smul_eq_mul,
      Fin.sum_univ_two] using this
  have hMQ : M' * Q_mat = Q_mat * Matrix.diagonal ![s, s⁻¹] := by
    ext i j
    simp only [Q_mat, Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Fin.sum_univ_two]
    fin_cases j
    · simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false, mul_zero,
        add_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination d⁻¹ * hv₁_eq i
    · simp (config := { decide := true }) only [Fin.isValue, ite_true, ite_false, mul_zero,
        zero_add, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination hv₂_eq i
  have hQinv_mul : Q_mat⁻¹ * Q_mat = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [isUnit_iff_ne_zero, hQ_det]; exact one_ne_zero)
  refine ⟨Q⁻¹, ?_⟩
  have hQinv_val : (Q⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 = Q_mat.adjugate := rfl
  have hadj : Q_mat.adjugate = Q_mat⁻¹ := by
    rw [Matrix.inv_def, hQ_det, Ring.inverse_one, one_smul]
  have hQinv_inv_val : (Q⁻¹⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 = Q_mat := by
    rw [inv_inv]
  show (Q⁻¹ * M * Q⁻¹⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 = Matrix.diagonal ![s, s⁻¹]
  show (Q⁻¹).1 * M.1 * (Q⁻¹⁻¹).1 = Matrix.diagonal ![s, s⁻¹]
  rw [hQinv_val, hadj, hQinv_inv_val]
  calc Q_mat⁻¹ * M' * Q_mat
      = Q_mat⁻¹ * (M' * Q_mat) := by rw [Matrix.mul_assoc]
    _ = Q_mat⁻¹ * (Q_mat * Matrix.diagonal ![s, s⁻¹]) := by rw [hMQ]
    _ = Q_mat⁻¹ * Q_mat * Matrix.diagonal ![s, s⁻¹] := by rw [Matrix.mul_assoc]
    _ = 1 * Matrix.diagonal ![s, s⁻¹] := by rw [hQinv_mul]
    _ = Matrix.diagonal ![s, s⁻¹] := by rw [Matrix.one_mul]

/-- The source diagonalization theorem with the original scalar hypothesis. -/
theorem eigenvalues_implies_conj_to_diag (s : F) (hs : s ≠ s⁻¹)
    (M : Matrix.SpecialLinearGroup (Fin 2) F) (hM : HasEigenvalues M s) :
    ∃ P : Matrix.SpecialLinearGroup (Fin 2) F,
      (P * M * P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F).1 =
        Matrix.diagonal ![s, s⁻¹] := by
  have hs0 : s ≠ 0 := fun h => hs (by simp [h])
  exact (isConj_diag2_iff M s hs0).mp
    (eigenvalues_implies_isConj_diag2 s hs M hM hs0)

/-- A normal subgroup of `SL₂(F)` containing one matrix with eigenvalues `s`
and `s⁻¹`, with `s ≠ s⁻¹`, contains every matrix with those eigenvalues. -/
theorem normal_contains_all_with_eigenvalues
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hN : N.Normal) (s : F) (hs : s ≠ s⁻¹)
    (B : Matrix.SpecialLinearGroup (Fin 2) F) (hB : B ∈ N)
    (hBeig : HasEigenvalues B s)
    (Q : Matrix.SpecialLinearGroup (Fin 2) F)
    (hQeig : HasEigenvalues Q s) :
    Q ∈ N :=
  normal_subgroup_contains_all_conj_to_diag N hN s B hB
    (eigenvalues_implies_conj_to_diag s hs B hBeig) Q
    (eigenvalues_implies_conj_to_diag s hs Q hQeig)

end SL2
