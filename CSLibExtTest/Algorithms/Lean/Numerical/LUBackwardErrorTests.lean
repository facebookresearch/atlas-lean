/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.LUBackwardError
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

@[expose] public section

open Cslib.Algorithms.Lean.FloatingPoint Cslib.Algorithms.Lean.FloatingPoint.LUBackwardError

namespace CSLibExtTest.Algorithms.Lean.Numerical.LUBackwardErrorTests

/-- The predicate is satisfiable: the `1 × 1` real matrix `(3)` is factored as `(1)(3)` in double
precision. -/
example : IsFlLU 53 (fun _ _ : Fin 1 => (3 : ℝ)) (fun _ _ => 1) (fun _ _ => 3) :=
  isFlLU_one_by_one 53 3

/-- With no products to subtract, `subDotFl` returns its starting value unrounded. -/
example (c : ℝ) (a b : ℕ → ℝ) : subDotFl 53 c a b 0 = c := rfl

/-- One step of `subDotFl` rounds the product and then the difference. -/
example (c : ℝ) (a b : ℕ → ℝ) :
    subDotFl 53 c a b 1 = fl 53 (c - fl 53 (a 0 * b 0)) := rfl

/-- The backward error theorem applies to the `1 × 1` factorization of `(3)` in double precision,
where the pivot `3` is nonzero. -/
example : ∃ E : Matrix (Fin 1) (Fin 1) ℝ,
    (Matrix.of fun _ _ => (1 : ℝ)) * Matrix.of (fun _ _ => 3) = Matrix.of (fun _ _ => 3) + E ∧
      ∀ i j, |E i j| ≤ DotProductError.gamma 53 1 *
        ∑ k, |(Matrix.of fun _ _ : Fin 1 => (1 : ℝ)) i k| *
          |(Matrix.of fun _ _ : Fin 1 => (3 : ℝ)) k j| :=
  exists_mul_eq_add_abs_le_gamma (by norm_num) (isFlLU_one_by_one 53 3) (fun _ _ => by norm_num)

/-- `1` is a double-precision number. -/
theorem fl53_one : fl 53 (1 : ℝ) = 1 :=
  fl_eq_self (by norm_num) ⟨1, 0, by norm_num, by norm_num⟩

/-- `2` is a double-precision number. -/
theorem fl53_two : fl 53 (2 : ℝ) = 2 :=
  fl_eq_self (by norm_num) ⟨2, 0, by norm_num, by norm_num⟩

/-- A `2 × 2` instance exercising both Doolittle formulas: `A = [[2, 1], [4, 3]]` has the
floating-point factors `L = [[1, 0], [2, 1]]` and `U = [[2, 1], [0, 1]]`, every operation being
exact (`4 / 2 = 2`, `3 - 2 · 1 = 1`). -/
theorem isFlLU_two_by_two :
    IsFlLU 53 (!![2, 1; 4, 3] : Matrix (Fin 2) (Fin 2) ℝ) !![1, 0; 2, 1] !![2, 1; 0, 1] where
  diag_L i := by fin_cases i <;> rfl
  L_upper_zero i j h := by fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  U_lower_zero i j h := by fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  U_eq i j h := by
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact absurd h (by decide)
    · simp [subDotFl, rowSeq, colSeq, fl53_two]
      norm_num [fl53_one]
  L_eq i j h := by
    fin_cases i <;> fin_cases j
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp [subDotFl]
      norm_num [fl53_two]
    · exact absurd h (by decide)

/-- The backward error theorem on the `2 × 2` instance. -/
example : ∃ E : Matrix (Fin 2) (Fin 2) ℝ,
    (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![2, 1; 0, 1] = !![2, 1; 4, 3] + E ∧
      ∀ i j, |E i j| ≤ DotProductError.gamma 53 2 *
        ∑ k, |(!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℝ) i k| *
          |(!![2, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) k j| :=
  exists_mul_eq_add_abs_le_gamma (by norm_num) isFlLU_two_by_two fun j hj => by
    fin_cases j
    · norm_num
    · exact absurd hj (by decide)

end CSLibExtTest.Algorithms.Lean.Numerical.LUBackwardErrorTests
