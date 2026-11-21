/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.UnitaryErrorBudget
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open MathlibExt.Quantum.UnitaryErrorBudget

namespace MathlibExt.Quantum.UnitaryErrorBudgetTests

/-- Equal gate lists have zero total error. -/
example {n : Type*} [Fintype n] [DecidableEq n] {T : ℕ}
    (U : Fin T → Matrix n n ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup n ℂ) :
    ‖(List.ofFn U).prod - (List.ofFn U).prod‖ ≤ ∑ _i : Fin T, (0 : ℝ) :=
  norm_circuit_sub_le U U hU hU (fun _ => 0) (fun i => by simp)

/-- Replacing one gate by the identity costs at most that gate's distance
from the identity. -/
theorem drop_one_gate {n : Type*} [Fintype n] [DecidableEq n] {T : ℕ}
    (U : Fin T → Matrix n n ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup n ℂ) (j : Fin T) :
    ‖(List.ofFn U).prod - (List.ofFn (Function.update U j 1)).prod‖ ≤
      ‖U j - 1‖ := by
  have hV : ∀ i, Function.update U j 1 i ∈ Matrix.unitaryGroup n ℂ := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      exact one_mem _
    · rw [Function.update_of_ne hij]
      exact hU i
  have hε : ∀ i, ‖U i - Function.update U j 1 i‖ ≤
      (if i = j then ‖U j - 1‖ else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      simp
    · simp [hij]
  have h := norm_circuit_sub_le U (Function.update U j 1) hU hV _ hε
  rw [Finset.sum_ite_eq'] at h
  simp only [Finset.mem_univ, ite_true] at h
  exact h

/-- A two-dimensional phase gate is unitary. -/
theorem phase_diagonal_mem_unitaryGroup (φ : ℝ) :
    Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] ∈
      Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have he : (starRingEnd ℂ) (Complex.exp (φ * Complex.I)) *
      Complex.exp (φ * Complex.I) = 1 := by
    rw [RCLike.conj_mul, Complex.norm_exp_ofReal_mul_I φ]
    simp
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  have hw : (fun i : Fin 2 =>
        star (![1, Complex.exp (φ * Complex.I)] : Fin 2 → ℂ) i *
          ![1, Complex.exp (φ * Complex.I)] i) = fun _ => 1 := by
    funext i
    fin_cases i <;> simp [he]
  rw [hw, Matrix.diagonal_one]

/-- The phase-gate distance from the identity is the scalar phase distance. -/
theorem phase_diagonal_sub_one_norm (φ : ℝ) :
    ‖(Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
        Matrix (Fin 2) (Fin 2) ℂ) - 1‖ =
      ‖Complex.exp (φ * Complex.I) - 1‖ := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal (fun _ => 1) := Matrix.diagonal_one.symm
  have hsub : (Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
        Matrix (Fin 2) (Fin 2) ℂ) - 1 =
      Matrix.diagonal ![0, Complex.exp (φ * Complex.I) - 1] := by
    rw [h1, Matrix.diagonal_sub]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [hsub, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    fin_cases i <;> simp
  · have h1 : (![0, Complex.exp (φ * Complex.I) - 1] : Fin 2 → ℂ) 1 =
        Complex.exp (φ * Complex.I) - 1 := by simp
    rw [← h1]
    exact norm_le_pi_norm _ _

/-- The first-coordinate diagonal matrix is an orthogonal projection. -/
theorem diagonal_one_zero_isStarProjection :
    IsStarProjection
      (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [isStarProjection_iff']
  constructor
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    fin_cases i <;> simp

/-- Empty circuits have zero mutual error. -/
example {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Fin 0 → Matrix n n ℂ) :
    ‖(List.ofFn U).prod - (List.ofFn V).prod‖ ≤ (0 : ℝ) := by
  simp only [List.ofFn_zero, List.prod_nil, sub_self, norm_zero, le_refl]

/-- In dimension zero, every pair of unitaries has zero mutual distance. -/
example (U V : Matrix (Fin 0) (Fin 0) ℂ) : ‖U - V‖ = 0 := by
  have h : U = V := Subsingleton.elim _ _
  rw [h, sub_self, norm_zero]

#print axioms norm_list_ofFn_prod_sub_le
#print axioms norm_circuit_sub_le
#print axioms norm_inner_conj_sub_le
#print axioms norm_inner_circuit_conj_sub_le

end MathlibExt.Quantum.UnitaryErrorBudgetTests
