/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.SpecialUnitaryFinTwo
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped Matrix

/-!
# Tests for complex special unitary matrices of size two

Exercise conjugate-entry orientation, both scalar signs, the sharp trace bound,
and a matrix excluded by special-unitary membership.
-/

-- The public form theorem determines both conjugate entries without unfolding the carrier.
example (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    M 1 0 = -starRingEnd ℂ (M 0 1) ∧ M 1 1 = starRingEnd ℂ (M 0 0) := by
  obtain ⟨a, b, rfl, _⟩ := Matrix.exists_eq_of_mem_specialUnitaryGroup_fin_two M hM
  simp

-- The two scalar signs have the expected matrix traces.
example : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
  norm_num [Matrix.trace_fin_two]

example : Matrix.trace (-1 : Matrix (Fin 2) (Fin 2) ℂ) = -2 := by
  norm_num [Matrix.trace_fin_two]

-- Identity is a real-trace example and attains the trace-norm bound.
example : (Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ)).im = 0 :=
  Matrix.trace_im_eq_zero_of_mem_specialUnitaryGroup_fin_two 1
    (Submonoid.one_mem (Matrix.specialUnitaryGroup (Fin 2) ℂ))

example : ‖Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ = 2 := by
  norm_num [Matrix.trace_fin_two]

example : ‖Matrix.trace (-1 : Matrix (Fin 2) (Fin 2) ℂ)‖ = 2 := by
  norm_num [Matrix.trace_fin_two]

example : ‖Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 :=
  Matrix.norm_trace_le_two_of_mem_specialUnitaryGroup_fin_two 1
    (Submonoid.one_mem (Matrix.specialUnitaryGroup (Fin 2) ℂ))

private theorem neg_identity_mem :
    (-1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · simp
  · simp [Matrix.det_neg]

-- The central negative identity is represented in the canonical group subtype.
example :
    (⟨(-1 : Matrix (Fin 2) (Fin 2) ℂ), neg_identity_mem⟩ :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) ∈
      Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  apply (Matrix.mem_center_specialUnitaryGroup_fin_two_iff _).mpr
  exact Or.inr rfl

-- The zero matrix cannot satisfy the determinant-one condition.
example : (0 : Matrix (Fin 2) (Fin 2) ℂ) ∉ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  intro h
  have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp h).2
  norm_num [Matrix.det_fin_two] at hdet

#print axioms Matrix.exists_eq_of_mem_specialUnitaryGroup_fin_two
#print axioms Matrix.trace_im_eq_zero_of_mem_specialUnitaryGroup_fin_two
#print axioms Matrix.norm_trace_le_two_of_mem_specialUnitaryGroup_fin_two
#print axioms Matrix.mem_center_specialUnitaryGroup_fin_two_iff
