/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasAlternatingSquaredBinomialSum

/-! # Tests for squared-binomial sums with Lucas sequences -/

open MetaMathlibExt

-- For `p = 2`, `n = 2`, the unsigned convolution is `2 · 2 + 4 · 1 · 2 = 12`.
example :
    ∑ k ∈ Finset.range (2 + 1),
        ((2 : ℕ).choose k : ℤ) ^ 2 * lucasU ⟨2, -1, by decide⟩ (2 - k) *
          lucasV ⟨2, -1, by decide⟩ k = 12 := by
  rw [lucasU_lucasV_sum_choose_sq (p := 2) (n := 2)]
  decide

-- The sign of `p` is unrestricted; here `U₂ = -3`.
example :
    ∑ k ∈ Finset.range (2 + 1),
        ((2 : ℕ).choose k : ℤ) ^ 2 * lucasU ⟨-3, -1, by decide⟩ (2 - k) *
          lucasV ⟨-3, -1, by decide⟩ k = -18 := by
  rw [lucasU_lucasV_sum_choose_sq (p := -3) (n := 2)]
  decide

-- At `n = 0` both sides vanish for every `p`.
example (p : ℤ) :
    ∑ k ∈ Finset.range (0 + 1),
        ((0 : ℕ).choose k : ℤ) ^ 2 * lucasU ⟨p, -1, by decide⟩ (0 - k) *
          lucasV ⟨p, -1, by decide⟩ k = 0 := by
  rw [lucasU_lucasV_sum_choose_sq (p := p) (n := 0)]
  rfl

-- Pell case `p = 2`, `n = 2`, computed directly: the Pell numbers `U = 0, 1, 2, 5, 12` and the
-- Pell–Lucas numbers `V = 2, 2, 6, 14, 34` give `24 - 160 + 432 - 224 + 0 = 72`.
example :
    ∑ k ∈ Finset.range (2 * 2 + 1),
        ((2 * 2).choose k : ℤ) ^ 2 * (-1) ^ k *
          lucasU ⟨2, -1, by decide⟩ (2 * 2 - k) * lucasV ⟨2, -1, by decide⟩ k = 72 := by
  decide

-- The theorem gives the same value from the right side `(-1)^2 C(4, 2) U_4 = 6 * 12`.
example :
    ∑ k ∈ Finset.range (2 * 2 + 1),
        ((2 * 2).choose k : ℤ) ^ 2 * (-1) ^ k *
          lucasU ⟨2, -1, by decide⟩ (2 * 2 - k) * lucasV ⟨2, -1, by decide⟩ k = 72 := by
  rw [lucasU_lucasV_sum_choose_sq_alternating]
  decide

-- The parameter may be negative: for `p = -3` and `n = 1` the right side is
-- `-C(2, 1) U_2 = -2 * (-3) = 6`.
example :
    ∑ k ∈ Finset.range (2 * 1 + 1),
        ((2 * 1).choose k : ℤ) ^ 2 * (-1) ^ k *
          lucasU ⟨-3, -1, by decide⟩ (2 * 1 - k) * lucasV ⟨-3, -1, by decide⟩ k = 6 := by
  rw [lucasU_lucasV_sum_choose_sq_alternating]
  decide

-- For `n = 0` the sum is the single term `U_0 V_0 = 0`, matching `U_0 = 0`.
example (p : ℤ) :
    ∑ k ∈ Finset.range (2 * 0 + 1),
        ((2 * 0).choose k : ℤ) ^ 2 * (-1) ^ k *
          lucasU ⟨p, -1, by decide⟩ (2 * 0 - k) * lucasV ⟨p, -1, by decide⟩ k = 0 := by
  rw [lucasU_lucasV_sum_choose_sq_alternating]
  rfl

-- The Fibonacci case `p = 1`: with the Fibonacci numbers `F` and the Lucas numbers `L`,
-- `∑_{k=0}^{2n} (-1)^k C(2n, k)^2 F_{2n-k} L_k = (-1)^n C(2n, n) F_{2n}`.
example (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℤ) ^ 2 * (-1) ^ k * (Nat.fib (2 * n - k) : ℤ) * (lucasNumber k : ℤ) =
      (-1) ^ n * ((2 * n).choose n : ℤ) * Nat.fib (2 * n) := by
  simp only [← lucasU_fibonacciLucasParams, ← lucasV_fibonacciLucasParams]
  exact lucasU_lucasV_sum_choose_sq_alternating 1 n

private def symmWeights (k : ℕ) : ℤ := if k = 1 then -5 else 2

-- At `P = 3`, `Q = 2`, and `m = 2`, the signed weights give summands `12`, `-15`, and `0`.
-- Exercise the public lemma and independently compute both sides.
example :
    let lhs := ∑ k ∈ Finset.range (2 + 1), symmWeights k * lucasU ⟨3, 2, by decide⟩ (2 - k) *
      lucasV ⟨3, 2, by decide⟩ k
    let rhs := (∑ k ∈ Finset.range (2 + 1), symmWeights k) * lucasU ⟨3, 2, by decide⟩ 2
    lhs = rhs ∧ lhs = -3 ∧ rhs = -3 := by
  have hsym : ∀ k ≤ 2, symmWeights (2 - k) = symmWeights k := by
    intro k hk
    have h : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide
  exact ⟨sum_mul_lucasU_mul_lucasV_of_symm ⟨3, 2, by decide⟩ 2 symmWeights hsym,
    by decide, by decide⟩
