/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.SpecialUnitaryFinTwo
import MathlibExt.GroupTheory.SU2Basic

/-!
# Regression tests for the canonical SU(2) center

Exercise both scalar signs, two noncentral matrices, and the canonical
characterization of a central matrix. Membership fixtures use existing APIs.
-/

namespace Matrix

private theorem diag_I_mem_specialUnitaryGroup :
    !![Complex.I, (0 : ℂ); 0, -Complex.I] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  SU2.diag_I_mem

private theorem quarterTurn_mem_specialUnitaryGroup :
    !![(0 : ℂ), 1; -1, 0] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  SU2.antidiag_mem

-- The identity is central in `SU(2)`.
example : (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
    Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [mem_center_specialUnitaryGroup_fin_two_iff]
  exact Or.inl rfl

-- Negating the identity is central in `SU(2)`.
example : (⟨-1, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff']; simp
    · simp [Matrix.det_fin_two]⟩ :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
    Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [mem_center_specialUnitaryGroup_fin_two_iff]
  exact Or.inr rfl

-- The diagonal matrix `diag(i, -i)` is not central: its `(0, 0)` entry is `i`,
-- which is neither `1` nor `-1`.
example : (⟨!![Complex.I, (0 : ℂ); 0, -Complex.I], diag_I_mem_specialUnitaryGroup⟩ :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∉
    Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [mem_center_specialUnitaryGroup_fin_two_iff]
  rintro (h | h) <;> have h00 := congr_fun (congr_fun h 0) 0 <;>
    simp [Matrix.of_apply, Complex.ext_iff] at h00

-- The quarter-turn matrix is not central: its `(0, 1)` entry is `1`, while both
-- `±1` have `(0, 1)` entry `0`.
example : (⟨!![(0 : ℂ), 1; -1, 0], quarterTurn_mem_specialUnitaryGroup⟩ :
    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∉
    Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  rw [mem_center_specialUnitaryGroup_fin_two_iff]
  rintro (h | h) <;> have h01 := congr_fun (congr_fun h 0) 1 <;>
    simp [Matrix.of_apply] at h01

-- Every central element of `SU(2)` is `±1` as a matrix.
example (M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (hM : M ∈ Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (M : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (M : Matrix (Fin 2) (Fin 2) ℂ) = -1 :=
  (mem_center_specialUnitaryGroup_fin_two_iff M).mp hM

#print axioms Matrix.mem_center_specialUnitaryGroup_fin_two_iff
#print axioms diag_I_mem_specialUnitaryGroup
#print axioms quarterTurn_mem_specialUnitaryGroup

end Matrix
