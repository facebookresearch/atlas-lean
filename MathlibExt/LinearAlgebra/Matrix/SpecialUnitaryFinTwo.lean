/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Complex special unitary matrices of size two

Code-derived port of the matrix-form, center and trace results in
`v1/Atlas/AlgebraNotes/code/SimpleGroups.lean` at ATLAS commit
`8de8f74fa5760eb8b768a9804494ca2ab631cf87`, lines 133–315.
This module does not claim comparison with the printed textbook source.
-/

@[expose] public section

set_option autoImplicit false
open scoped Matrix

namespace Matrix

private theorem conjTranspose_eq_adjugate_of_mem_specialUnitaryGroup_fin_two
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ specialUnitaryGroup (Fin 2) ℂ) :
    star M = M.adjugate := by
  have hdet : M.det = 1 := (mem_specialUnitaryGroup_iff.mp hM).2
  have hunit : star M * M = 1 := hM.1.1
  have hinv : M⁻¹ = M.adjugate := by
    rw [Matrix.inv_def, hdet]
    simp [Ring.inverse_one]
  exact (Matrix.inv_eq_left_inv hunit).symm.trans hinv

private theorem diagonal_conjugate_of_mem_specialUnitaryGroup_fin_two
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ specialUnitaryGroup (Fin 2) ℂ) :
    M 1 1 = starRingEnd ℂ (M 0 0) := by
  have h := congrFun
    (congrFun (conjTranspose_eq_adjugate_of_mem_specialUnitaryGroup_fin_two M hM) 0) 0
  simpa [Matrix.adjugate_fin_two] using h.symm

private theorem lower_left_eq_neg_conj_of_star_eq_adjugate
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hstar : star M = M.adjugate) : M 1 0 = -starRingEnd ℂ (M 0 1) := by
  have h := congrFun (congrFun hstar 0) 1
  simp [Matrix.adjugate_fin_two] at h
  have hconj := congrArg (starRingEnd ℂ) h
  simpa using hconj

private theorem normSq_row_eq_one_of_mem_specialUnitaryGroup_fin_two
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ specialUnitaryGroup (Fin 2) ℂ) :
    Complex.normSq (M 0 0) + Complex.normSq (M 0 1) = 1 := by
  have h := congrFun (congrFun hM.1.2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h
  rw [Complex.mul_conj, Complex.mul_conj] at h
  simpa using congrArg Complex.re h

/-- A complex special unitary matrix of size two has the standard conjugate-entry form. -/
theorem exists_eq_of_mem_specialUnitaryGroup_fin_two
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ∃ a b : ℂ, M = !![a, b; -starRingEnd ℂ b, starRingEnd ℂ a] ∧
      Complex.normSq a + Complex.normSq b = 1 := by
  have h10 := lower_left_eq_neg_conj_of_star_eq_adjugate M
    (conjTranspose_eq_adjugate_of_mem_specialUnitaryGroup_fin_two M hM)
  have h11 := diagonal_conjugate_of_mem_specialUnitaryGroup_fin_two M hM
  refine ⟨M 0 0, M 0 1, ?_, normSq_row_eq_one_of_mem_specialUnitaryGroup_fin_two M hM⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h11]

/-- The trace of a complex special unitary matrix of size two is real. -/
theorem trace_im_eq_zero_of_mem_specialUnitaryGroup_fin_two
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ specialUnitaryGroup (Fin 2) ℂ) :
    (Matrix.trace M).im = 0 := by
  obtain ⟨a, b, hform, _⟩ := exists_eq_of_mem_specialUnitaryGroup_fin_two M hM
  rw [hform, Matrix.trace_fin_two]
  simp

/-- The complex trace of a special unitary matrix of size two has norm at most two. -/
theorem norm_trace_le_two_of_mem_specialUnitaryGroup_fin_two
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ‖Matrix.trace M‖ ≤ 2 := by
  obtain ⟨a, b, hform, hnorm⟩ := exists_eq_of_mem_specialUnitaryGroup_fin_two M hM
  rw [hform, Matrix.trace_fin_two]
  change ‖a + starRingEnd ℂ a‖ ≤ 2
  rw [Complex.add_conj]
  simp [Real.norm_eq_abs]
  apply abs_le_of_sq_le_sq _ (by norm_num)
  have hnorm' : a.re ^ 2 + a.im ^ 2 + Complex.normSq b = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hnorm
  nlinarith [Complex.normSq_nonneg b, sq_nonneg a.im]

private theorem diagonal_I_mem_specialUnitaryGroup_fin_two :
    !![Complex.I, (0 : ℂ); 0, -Complex.I] ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.det_fin_two]

private theorem skew_mem_specialUnitaryGroup_fin_two :
    !![(0 : ℂ), 1; -1, 0] ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.det_fin_two]

/-- The center of the complex special unitary group of size two consists of the two scalar signs. -/
theorem mem_center_specialUnitaryGroup_fin_two_iff
    (M : specialUnitaryGroup (Fin 2) ℂ) :
    M ∈ Subgroup.center (specialUnitaryGroup (Fin 2) ℂ) ↔
      (M : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (M : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  constructor
  · intro hM
    rw [Subgroup.mem_center_iff] at hM
    have comm_of (g : Matrix (Fin 2) (Fin 2) ℂ)
        (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) :
        (M : Matrix (Fin 2) (Fin 2) ℂ) * g = g * (M : Matrix (Fin 2) (Fin 2) ℂ) := by
      have h := congrArg Subtype.val (hM ⟨g, hg⟩)
      simpa only [Submonoid.coe_mul] using h.symm
    obtain ⟨a, b, hform, _⟩ := exists_eq_of_mem_specialUnitaryGroup_fin_two
      (M : Matrix (Fin 2) (Fin 2) ℂ) M.prop
    have hb : b = 0 := by
      have h := congrFun (congrFun (comm_of _ diagonal_I_mem_specialUnitaryGroup_fin_two) 0) 1
      rw [hform] at h
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h
      have hzero : (2 : ℂ) * (Complex.I * b) = 0 := by
        linear_combination -h
      have hi : Complex.I * b = 0 :=
        (mul_eq_zero.mp hzero).resolve_left (by norm_num)
      exact (mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero
    have ha : a = starRingEnd ℂ a := by
      have h := congrFun (congrFun (comm_of _ skew_mem_specialUnitaryGroup_fin_two) 0) 1
      rw [hform] at h
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hb] using h
    have hdet : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
      (mem_specialUnitaryGroup_iff.mp M.prop).2
    rw [hform, Matrix.det_fin_two] at hdet
    have hsq : a * a = 1 := by simpa [hb, ← ha] using hdet
    rcases mul_self_eq_one_iff.mp hsq with hpos | hneg
    · left
      rw [hform]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hpos]
    · right
      rw [hform]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hneg]
  · intro hM
    rw [Subgroup.mem_center_iff]
    intro g
    ext1
    simp only [Submonoid.coe_mul]
    rcases hM with hpos | hneg
    · simp [hpos]
    · simp [hneg]

end Matrix
