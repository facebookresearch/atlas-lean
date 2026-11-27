/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasDixonBinomialSum

/-! # Tests for the Dixon-type alternating binomial sum with Lucas sequences -/

open MetaMathlibExt

-- At `p = -3` and `n = 1`, the terms are `-6`, `24`, and `0`.
example :
    ∑ k ∈ Finset.range (2 * 1 + 1),
        ((2 * 1).choose k : ℤ) ^ 3 * (-1) ^ k *
          lucasU ⟨-3, -1, by decide⟩ (2 * 1 - k) * lucasV ⟨-3, -1, by decide⟩ k = 18 := by
  decide

-- The theorem gives the same value from `-C(3, 1) C(2, 1) U₂ = -6 * (-3)`.
example :
    ∑ k ∈ Finset.range (2 * 1 + 1),
        ((2 * 1).choose k : ℤ) ^ 3 * (-1) ^ k *
          lucasU ⟨-3, -1, by decide⟩ (2 * 1 - k) * lucasV ⟨-3, -1, by decide⟩ k = 18 := by
  rw [lucasU_lucasV_sum_choose_cube_alternating]
  decide

-- At `n = 0`, the only summand is zero for every integer parameter.
example (p : ℤ) :
    ∑ k ∈ Finset.range (2 * 0 + 1),
        ((2 * 0).choose k : ℤ) ^ 3 * (-1) ^ k *
          lucasU ⟨p, -1, by decide⟩ (2 * 0 - k) * lucasV ⟨p, -1, by decide⟩ k = 0 := by
  rw [lucasU_lucasV_sum_choose_cube_alternating]
  rfl

-- At `p = 1`, the formula specializes to Fibonacci and Lucas numbers.
example (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℤ) ^ 3 * (-1) ^ k * (Nat.fib (2 * n - k) : ℤ) * (lucasNumber k : ℤ) =
      (-1) ^ n * ((3 * n).choose n * (2 * n).choose n : ℕ) * (Nat.fib (2 * n) : ℤ) := by
  simp only [← lucasU_fibonacciLucasParams, ← lucasV_fibonacciLucasParams]
  exact lucasU_lucasV_sum_choose_cube_alternating 1 n
