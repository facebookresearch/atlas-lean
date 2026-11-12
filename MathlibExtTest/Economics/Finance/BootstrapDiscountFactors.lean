/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.BootstrapDiscountFactors
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for bootstrap uniqueness

The lower-triangular cash-flow matrix `!![1, 0; 1, 1]` has diagonal `1, 1`,
so it determines discount factors uniquely; it sends `![1, 1/2]` to
`![1, 3/2]`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.BootstrapDiscountFactors

open MathlibExt.Economics.Finance

-- Test section (required): concrete evaluations with all hypotheses proved.

/-- The concrete matrix is lower-triangular. -/
example : (!![(1:ℝ), 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsLowerTriangular := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at ⊢ <;> exact absurd h (by decide)

/-- Its diagonal entries are nonzero. -/
example : ∀ i, (!![(1:ℝ), 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) i i ≠ 0 := by
  intro i
  fin_cases i <;> simp

/-- Hence discount factors are unique for this matrix. -/
example (D₁ D₂ : Fin 2 → ℝ)
    (h : (!![(1:ℝ), 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).mulVec D₁ =
         (!![(1:ℝ), 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).mulVec D₂) :
    D₁ = D₂ := by
  have hC : (!![(1:ℝ), 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsLowerTriangular := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp at ⊢ <;> exact absurd hj (by decide)
  have hdiag : ∀ i, (!![(1:ℝ), 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) i i ≠ 0 := by
    intro i
    fin_cases i <;> simp
  exact bootstrap_discountFactors_unique hC hdiag h

/-- Direct computation of discounted prices. -/
example : (!![(1:ℝ), 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![1, 1/2] = ![1, 3/2] := by
  ext i
  fin_cases i
  · simp [Matrix.mulVec]
  · simp [Matrix.mulVec]
    norm_num

end MathlibExtTest.Economics.Finance.BootstrapDiscountFactors
