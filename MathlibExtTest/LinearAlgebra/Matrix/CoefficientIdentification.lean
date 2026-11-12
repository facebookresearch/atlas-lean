/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.CoefficientIdentification

/-!
# Tests for identification of regression coefficients

A `3 × 2` design with proportional columns gives two coefficient vectors with the same mean, so it
does not identify; a design with a zero column does not identify either (both through
`exists_ne_mulVec_eq_of_not_linearIndependent`); a `3 × 2` design with independent columns does.
-/

@[expose] public section

open Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.CoefficientIdentification

open _root_.MathlibExt.CoefficientIdentification

/-- Singular design: every row is `[1, 2]`. -/
def X₁ : Matrix (Fin 3) (Fin 2) ℝ := !![1, 2; 1, 2; 1, 2]

/-- Full-column-rank design. -/
def X₂ : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 1, 1]

theorem X₁_mulVec_eq : X₁ *ᵥ ![2, 0] = X₁ *ᵥ ![0, 1] := by
  ext i
  fin_cases i <;> simp [X₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem X₁_vec_ne : (![2, 0] : Fin 2 → ℝ) ≠ ![0, 1] := by
  intro h
  have h0 := congrArg (fun v : Fin 2 → ℝ => v 0) h
  simp at h0

theorem X₁_not_identified : ¬ CoefficientsIdentified X₁ :=
  fun h => X₁_vec_ne (h _ _ X₁_mulVec_eq)

theorem X₂_identified : CoefficientsIdentified X₂ := by
  rw [coefficientsIdentified_iff, linearIndependent_fin2]
  constructor
  · intro h
    have h1 := congrArg (fun w : Fin 3 → ℝ => w 1) h
    simp [X₂, Matrix.col_apply] at h1
  · intro a h
    have h0 := congrArg (fun w : Fin 3 → ℝ => w 0) h
    simp [X₂, Matrix.col_apply] at h0

/-- Zero-column design: second column is zero. -/
def X₃ : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 0; 1, 0]

theorem X₃_col1_eq_zero : X₃.col 1 = 0 := by
  ext i
  fin_cases i <;> simp [X₃, Matrix.col_apply]

theorem X₃_not_linearIndependent : ¬ LinearIndependent ℝ X₃.col := by
  intro h
  exact (h.ne_zero 1) X₃_col1_eq_zero

theorem X₃_exists_ne_mulVec_eq :
    ∃ β β' : Fin 2 → ℝ, β ≠ β' ∧ X₃ *ᵥ β = X₃ *ᵥ β' :=
  exists_ne_mulVec_eq_of_not_linearIndependent X₃_not_linearIndependent

theorem X₁_not_linearIndependent : ¬ LinearIndependent ℝ X₁.col := by
  rw [← coefficientsIdentified_iff]
  exact X₁_not_identified

theorem X₁_exists_ne_mulVec_eq :
    ∃ β β' : Fin 2 → ℝ, β ≠ β' ∧ X₁ *ᵥ β = X₁ *ᵥ β' :=
  exists_ne_mulVec_eq_of_not_linearIndependent X₁_not_linearIndependent

end MathlibExtTest.LinearAlgebra.Matrix.CoefficientIdentification
