/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasShiftedBinomialConvolution

/-! # Tests for the Lucas convolution with shifted binomial weights -/

open MetaMathlibExt

-- At `p = -2` and `n = 2`, the three terms are `0`, `-32`, and `-24`.
example :
    ∑ k ∈ Finset.range (2 + 1),
        ((2 * 2).choose k * (2 * 2).choose (2 + k) : ℤ) *
          lucasU ⟨-2, -1, by decide⟩ k * lucasV ⟨-2, -1, by decide⟩ (2 - k) = -56 := by
  decide

-- The theorem gives the same value from `C(8, 2) U_2 = 28 * (-2)`.
example :
    ∑ k ∈ Finset.range (2 + 1),
        ((2 * 2).choose k * (2 * 2).choose (2 + k) : ℤ) *
          lucasU ⟨-2, -1, by decide⟩ k * lucasV ⟨-2, -1, by decide⟩ (2 - k) = -56 := by
  rw [lucasU_lucasV_sum_choose_two_n]
  decide

-- For `n = 0`, both sides vanish for every integer parameter.
example (p : ℤ) :
    ∑ k ∈ Finset.range (0 + 1),
        ((2 * 0).choose k * (2 * 0).choose (0 + k) : ℤ) *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (0 - k) = 0 := by
  rw [lucasU_lucasV_sum_choose_two_n]
  rfl

-- For `p = 1`, the formula specializes to Fibonacci and Lucas numbers.
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        ((2 * n).choose k * (2 * n).choose (n + k) : ℤ) *
          (Nat.fib k : ℤ) * (lucasNumber (n - k) : ℤ) = ((4 * n).choose n : ℤ) * Nat.fib n := by
  simp only [← lucasU_fibonacciLucasParams, ← lucasV_fibonacciLucasParams]
  exact lucasU_lucasV_sum_choose_two_n 1 n
