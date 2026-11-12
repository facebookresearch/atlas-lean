/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence

/-!
# Tests for real quadratic forms under congruence

The `2 × 2` Hamiltonian `H = !![2, 1; 1, 2]`: its eigenpairs `(3, ![1, 1])` and `(1, ![1, -1])`,
the orthogonality of the eigenvectors, positive definiteness from `posDef_two_by_two_of_pos`
(`a = 2` and `a * d - b ^ 2 = det H = 3`), and its quadratic form. A rotated symmetric `3 × 3`
stress tensor. The degenerate matrix `!![1, 1; 1, 1]` with kernel vector `![1, -1]`. The zero
vector and the zero matrix.
-/

@[expose] public section

open Matrix MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence

namespace MathlibExtTest.LinearAlgebra.Matrix.QuadraticFormCongruence

/-- `![1, 1]` is an eigenvector of `H = !![2, 1; 1, 2]` with eigenvalue `3`. -/
example : !![(2 : ℝ), 1; 1, 2] *ᵥ ![1, 1] = (3 : ℝ) • ![1, 1] := by
  ext i
  fin_cases i <;> norm_num

/-- `![1, -1]` is an eigenvector of `H` with eigenvalue `1`. -/
example : !![(2 : ℝ), 1; 1, 2] *ᵥ ![1, -1] = (1 : ℝ) • ![1, -1] := by
  ext i
  fin_cases i <;> norm_num

/-- The two eigenvectors of `H` are orthogonal. -/
example : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, -1] = 0 := by
  norm_num [dotProduct, Fin.sum_univ_two]

/-- The determinant of `H` is `3 = 2 * 2 - 1 ^ 2`, the second hypothesis of
`posDef_two_by_two_of_pos`. -/
example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).det = 3 := by
  rw [det_fin_two_of]
  norm_num

/-- `H` is positive definite by `posDef_two_by_two_of_pos` with `a = 2` and
`a * d - b ^ 2 = 3`. -/
example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef :=
  posDef_two_by_two_of_pos 2 1 2 (by norm_num) (by norm_num)

/-- The quadratic form of `H`. -/
example (x₀ x₁ : ℝ) :
    quadForm !![2, 1; 1, 2] ![x₀, x₁] = 2 * x₀ ^ 2 + 2 * x₀ * x₁ + 2 * x₁ ^ 2 := by
  rw [quadForm_two_by_two]
  ring

/-- A rotated symmetric `3 × 3` stress tensor: for symmetric `σ` and orthogonal `U`, the quadratic
form of `Uᵀ * σ * U` is that of `σ` at `U *ᵥ x`, the trace and the determinant are unchanged, and
`Uᵀ * σ * U` is symmetric. -/
example (σ U : Matrix (Fin 3) (Fin 3) ℝ) (hσ : σ.IsSymm)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    quadForm (Uᵀ * σ * U) x = quadForm σ (U *ᵥ x) ∧
      Matrix.trace (Uᵀ * σ * U) = Matrix.trace σ ∧
      Matrix.det (Uᵀ * σ * U) = Matrix.det σ ∧ (Uᵀ * σ * U).IsSymm :=
  ⟨quadForm_congr σ U x, trace_congr_of_mem_orthogonalGroup σ U hU,
    det_congr_of_mem_orthogonalGroup σ U hU, IsSymm_congr σ U hσ⟩

/-- `![1, -1]` is in the kernel of the degenerate matrix `!![1, 1; 1, 1]`. -/
private lemma degenerate_mulVec : !![(1 : ℝ), 1; 1, 1] *ᵥ ![1, -1] = 0 := by
  ext i
  fin_cases i <;> simp

/-- `A *ᵥ v = 0` for `A = !![1, 1; 1, 1]` and `v = ![1, -1]`. -/
example : !![(1 : ℝ), 1; 1, 1] *ᵥ ![1, -1] = 0 := degenerate_mulVec

/-- The quadratic form of `!![1, 1; 1, 1]` vanishes at `![1, -1]`. -/
example : quadForm !![(1 : ℝ), 1; 1, 1] ![1, -1] = 0 :=
  quadForm_eq_zero_of_mulVec_eq_zero _ _ degenerate_mulVec

/-- `!![1, 1; 1, 1]` is not positive definite. It has `0 < a = 1` but `a * d - b ^ 2 = 0`, so the
strict inequality in `posDef_two_by_two_of_pos` cannot be relaxed. -/
example : ¬ (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosDef :=
  not_posDef_of_mulVec_eq_zero _ _ degenerate_mulVec fun h => by simpa using congrFun h 0

/-- The quadratic form vanishes at the zero vector. -/
example {n : Type*} [Fintype n] (A : Matrix n n ℝ) : quadForm A 0 = 0 :=
  quadForm_eq_zero_of_mulVec_eq_zero A 0 (mulVec_zero A)

/-- The zero matrix has the zero quadratic form. -/
example {n : Type*} [Fintype n] (x : n → ℝ) : quadForm 0 x = 0 :=
  quadForm_eq_zero_of_mulVec_eq_zero 0 x (zero_mulVec x)

/-- `quadForm` has the same values as Mathlib's `Matrix.toQuadraticForm'`. -/
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (x : n → ℝ) :
    A.toQuadraticForm' x = quadForm A x := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', quadForm]

#print axioms quadForm
#print axioms quadForm_congr
#print axioms IsSymm_congr
#print axioms trace_congr_of_mem_orthogonalGroup
#print axioms det_congr_of_mem_orthogonalGroup
#print axioms quadForm_two_by_two
#print axioms posDef_two_by_two_of_pos
#print axioms quadForm_eq_zero_of_mulVec_eq_zero
#print axioms not_posDef_of_mulVec_eq_zero

end MathlibExtTest.LinearAlgebra.Matrix.QuadraticFormCongruence
