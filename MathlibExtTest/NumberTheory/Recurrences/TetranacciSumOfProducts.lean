/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Recurrences.TetranacciSumOfProducts
import Mathlib.Tactic.NormNum

/-! # Endpoint tests for the Tetranacci product sum -/

namespace MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted.Tests

variable (Q : ℤ → ℤ) (hQ : ∀ m : ℤ, Q (m + 4) = Q (m + 3) + Q (m + 2) + Q (m + 1) + Q m)

-- At n = 0 the two endpoint contributions cancel for arbitrary initial values.
example : 3 * (∑ k ∈ Finset.Icc (1 : ℕ) 0, Q k * (Q ((k : ℤ) - 2) + Q ((k : ℤ) - 3))) = 0 := by
  rw [three_mul_sum_tetranacci_mul_sub_two_add_sub_three Q hQ]
  simp

-- Initial values 1, 2, 3, 4 give 3 * (10 * (3 + 2) + 19 * (4 + 3)) = 549.
example (ha : Q (-3) = 1) (hb : Q (-2) = 2) (hc : Q (-1) = 3) (hd : Q 0 = 4) :
    3 * (∑ k ∈ Finset.Icc (1 : ℕ) 2, Q k * (Q ((k : ℤ) - 2) + Q ((k : ℤ) - 3))) = 549 := by
  have h₁ := hQ (-3)
  have h₂ := hQ (-2)
  have h₃ := hQ (-1)
  norm_num [ha, hb, hc, hd] at h₁
  norm_num [ha, hb, hc, hd, h₁] at h₂
  norm_num [ha, hb, hc, hd, h₁, h₂] at h₃
  rw [three_mul_sum_tetranacci_mul_sub_two_add_sub_three Q hQ]
  norm_num [ha, hb, hc, hd, h₁, h₂, h₃]

end MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted.Tests
