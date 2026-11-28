/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.LucasEvenCatalanConvolution

/-! # Tests for the even-index Catalan convolution with Lucas sequences -/

open MetaMathlibExt

-- At `p = -2` and `n = 2`, the terms are `0`, `-8`, and `-56`.
example :
    ∑ k ∈ Finset.range (2 + 1),
        (catalan (2 * 2 - 2 * k) * catalan (2 * k) : ℚ) *
          lucasU ⟨-2, -1, by decide⟩ k * lucasV ⟨-2, -1, by decide⟩ (2 - k) = -64 := by
  have hc : catalan 4 = 14 := by
    norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
  norm_num [Finset.sum_range_succ, hc, catalan_two, lucasU, lucasV]

-- The public theorem gives the same value from the closed form.
example :
    ∑ k ∈ Finset.range (2 + 1),
        (catalan (2 * 2 - 2 * k) * catalan (2 * k) : ℚ) *
          lucasU ⟨-2, -1, by decide⟩ k * lucasV ⟨-2, -1, by decide⟩ (2 - k) = -64 := by
  rw [lucasU_lucasV_sum_catalan_even]
  norm_num [catalan_three, lucasU]

-- At `n = 0`, the sum is zero for every integer parameter.
example (p : ℤ) :
    ∑ k ∈ Finset.range (0 + 1),
        (catalan (2 * 0 - 2 * k) * catalan (2 * k) : ℚ) *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (0 - k) = 0 := by
  rw [lucasU_lucasV_sum_catalan_even]
  simp [lucasU]

-- For `p = 1`, the formula specializes to Fibonacci and Lucas numbers.
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (catalan (2 * n - 2 * k) * catalan (2 * k) : ℚ) *
          (↑(Nat.fib k : ℤ) : ℚ) * (↑(lucasNumber (n - k) : ℤ) : ℚ) =
      (2 : ℚ) ^ (2 * n) / 2 * ((n + 2 : ℚ) / (2 * n + 1)) * catalan (n + 1) *
        (↑(Nat.fib n : ℤ) : ℚ) := by
  simp only [← lucasU_fibonacciLucasParams, ← lucasV_fibonacciLucasParams]
  exact lucasU_lucasV_sum_catalan_even 1 n
