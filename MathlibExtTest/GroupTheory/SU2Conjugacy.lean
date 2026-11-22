/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SU2Conjugacy
import MathlibExt.GroupTheory.SU2Basic
import Mathlib.Tactic

namespace MathlibExtTest.GroupTheory.SU2Conjugacy

open SU2

/-- The matrix form of the anti-diagonal element of `SU₂` is
`!![0, 1; -1, 0]`, with `α = 0` and `β = 1`. -/
example : ∃ α β : ℂ, α = 0 ∧ β = 1 ∧ Complex.normSq α + Complex.normSq β = 1 := by
  obtain ⟨α, β, hMat, hnorm⟩ :=
    Matrix.exists_eq_of_mem_specialUnitaryGroup_fin_two
      !![(0 : ℂ), 1; -1, 0] antidiag_mem
  have h00 := congr_fun (congr_fun hMat 0) 0
  have h01 := congr_fun (congr_fun hMat 0) 1
  simp at h00 h01
  exact ⟨α, β, h00.symm, h01.symm, hnorm⟩

/-- The matrix form of `diag(I, -I)` has `α = I` and `β = 0`. -/
example : ∃ α β : ℂ, α = Complex.I ∧ β = 0 ∧
    Complex.normSq α + Complex.normSq β = 1 := by
  obtain ⟨α, β, hMat, hnorm⟩ :=
    Matrix.exists_eq_of_mem_specialUnitaryGroup_fin_two
      !![Complex.I, (0 : ℂ); 0, -Complex.I] diag_I_mem
  have h00 := congr_fun (congr_fun hMat 0) 0
  have h01 := congr_fun (congr_fun hMat 0) 1
  simp at h00 h01
  exact ⟨α, β, h00.symm, h01.symm, hnorm⟩

/-- The identity of `SU₂` is central. -/
example : (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
    Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [Matrix.mem_center_specialUnitaryGroup_fin_two_iff]
  left
  rfl

/-- `diag(I, -I)` is not central in `SU₂`: it is neither `1` nor `-1`. -/
example : (⟨!![Complex.I, (0 : ℂ); 0, -Complex.I], diag_I_mem⟩ :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∉
    Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [Matrix.mem_center_specialUnitaryGroup_fin_two_iff]
  rw [not_or]
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simp at h00
    have him := congr_arg Complex.im h00
    simp at him
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simp at h00
    have him := congr_arg Complex.im h00
    simp at him

/-- The trace of the anti-diagonal element is real and has norm at most `2`
(it is `0`). -/
example :
    (Matrix.trace ((⟨!![(0 : ℂ), 1; -1, 0], antidiag_mem⟩ :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
      Matrix (Fin 2) (Fin 2) ℂ)).im = 0 ∧
      ‖Matrix.trace ((⟨!![(0 : ℂ), 1; -1, 0], antidiag_mem⟩ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 :=
  ⟨Matrix.trace_im_eq_zero_of_mem_specialUnitaryGroup_fin_two _ antidiag_mem,
    Matrix.norm_trace_le_two_of_mem_specialUnitaryGroup_fin_two _ antidiag_mem⟩

/-- The anti-diagonal element and `diag(I, -I)` both have trace `0`, so they
are conjugate in `SU₂`. -/
example : IsConj
    (⟨!![(0 : ℂ), 1; -1, 0], antidiag_mem⟩ :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (⟨!![Complex.I, (0 : ℂ); 0, -Complex.I], diag_I_mem⟩ :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  apply su2_conj_of_trace_eq
  simp [Matrix.trace_fin_two]

/-- Diagonalizing the anti-diagonal element gives a diagonal matrix of trace
`0`. -/
example : ∃ (D : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (z : ℂ),
    z * starRingEnd ℂ z = 1 ∧
    (D : Matrix (Fin 2) (Fin 2) ℂ) = !![z, (0 : ℂ); 0, starRingEnd ℂ z] ∧
    Matrix.trace (D : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  obtain ⟨D, ⟨z, hz, hD⟩, hconj⟩ := su2_conj_to_diag
    (⟨!![(0 : ℂ), 1; -1, 0], antidiag_mem⟩ :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
  refine ⟨D, z, hz, hD, ?_⟩
  rw [isConj_iff] at hconj
  obtain ⟨P, hP⟩ := hconj
  have htr : Matrix.trace (D : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.trace ((⟨!![(0 : ℂ), 1; -1, 0], antidiag_mem⟩ :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← hP]
    exact su2_trace_conj_inv P _
  rw [htr]
  simp [Matrix.trace_fin_two]

end MathlibExtTest.GroupTheory.SU2Conjugacy
