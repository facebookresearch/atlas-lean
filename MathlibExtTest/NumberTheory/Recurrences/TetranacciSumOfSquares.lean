/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Recurrences.TetranacciSumOfSquares
import Mathlib.Algebra.Group.End

/-! # Tests for the Tetranacci sum of squares with nonzero boundary terms -/

namespace MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted.Tests

/-- Shift a window of four consecutive terms forward, or solve for the oldest term to go back. -/
private def shift : Equiv.Perm (ℤ × ℤ × ℤ × ℤ) where
  toFun := fun ⟨a, b, c, d⟩ => (b, c, d, d + c + b + a)
  invFun := fun ⟨b, c, d, e⟩ => (e - d - c - b, b, c, d)
  left_inv := by
    rintro ⟨a, b, c, d⟩
    dsimp
    congr 1
    omega
  right_inv := by
    rintro ⟨b, c, d, e⟩
    dsimp
    simp only [Prod.mk.injEq, true_and]
    omega

/-- The two-sided sequence with values 4, 10, 19, 36 at indices 0 through 3. -/
private def Q (m : ℤ) : ℤ := ((shift ^ m) (4, 10, 19, 36)).1

private theorem recurrence (m : ℤ) :
    Q (m + 4) = Q (m + 3) + Q (m + 2) + Q (m + 1) + Q m := by
  simp only [Q, add_comm m _, zpow_add, Equiv.Perm.mul_apply]
  rfl

-- Check the negative-index terms that enter the lower endpoint.
example : (Q (-3), Q (-2), Q (-1)) = (1, 2, 3) := by decide

-- The endpoints cancel for the empty sum.
example : 3 * ∑ k ∈ Finset.Icc (1 : ℕ) 0, Q k ^ 2 = 0 := by
  rw [three_mul_sum_tetranacci_sq Q recurrence]
  decide

-- The left side is 3 * (10² + 19²). Reversing the sign of Q (-3) would add 4.
example : 3 * ∑ k ∈ Finset.Icc (1 : ℕ) 2, Q k ^ 2 = 1383 := by
  rw [three_mul_sum_tetranacci_sq Q recurrence]
  decide

end MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted.Tests
