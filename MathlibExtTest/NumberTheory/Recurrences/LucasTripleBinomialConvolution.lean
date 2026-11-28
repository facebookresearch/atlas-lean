/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasTripleBinomialConvolution

/-! # Tests for the Lucas convolution with triple binomial weights -/

open MetaMathlibExt

-- At `p = -2` and `n = 2`, the terms are `0`, `-48`, and `-24`.
example :
    ∑ k ∈ Finset.range (2 + 1),
        ((2 : ℕ).choose k * (2 * 2).choose (2 + k) * (2 + k).choose k : ℤ) *
          lucasU ⟨-2, -1, by decide⟩ k * lucasV ⟨-2, -1, by decide⟩ (2 - k) = -72 := by
  decide

-- The theorem gives the same value from `C(4, 2)^2 U_2 = 36 * (-2)`.
example :
    ∑ k ∈ Finset.range (2 + 1),
        ((2 : ℕ).choose k * (2 * 2).choose (2 + k) * (2 + k).choose k : ℤ) *
          lucasU ⟨-2, -1, by decide⟩ k * lucasV ⟨-2, -1, by decide⟩ (2 - k) = -72 := by
  rw [lucasU_lucasV_sum_choose_n_plus_k]
  decide

-- At `n = 0`, the sum is zero for every integer parameter.
example (p : ℤ) :
    ∑ k ∈ Finset.range (0 + 1),
        ((0 : ℕ).choose k * (2 * 0).choose (0 + k) * (0 + k).choose k : ℤ) *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (0 - k) = 0 := by
  rw [lucasU_lucasV_sum_choose_n_plus_k]
  rfl

-- For `p = 1`, the formula specializes to Fibonacci and Lucas numbers.
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k * (2 * n).choose (n + k) * (n + k).choose k : ℤ) *
          (Nat.fib k : ℤ) * (lucasNumber (n - k) : ℤ) =
      ((2 * n).choose n : ℤ) ^ 2 * Nat.fib n := by
  simp only [← lucasU_fibonacciLucasParams, ← lucasV_fibonacciLucasParams]
  exact lucasU_lucasV_sum_choose_n_plus_k 1 n
