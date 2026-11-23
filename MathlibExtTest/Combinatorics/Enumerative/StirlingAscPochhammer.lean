/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.StirlingAscPochhammer

/-!
# Tests for Stirling numbers of the first kind and the rising factorial

Concrete instances: `x (x + 1) (x + 2) = 2 x + 3 x² + x³`; the row sum `∑ₖ s(n, k) = n!`;
the empty product (`n = 0`); and the polynomial identity for `n = 2`.
-/

@[expose] public section

open Finset Polynomial

namespace MathlibExtTest.Combinatorics.Enumerative.StirlingAscPochhammer

/-- `n = 0`: the empty rising factorial is `1`. -/
example (x : ℚ) : ∑ k ∈ range 1, (Nat.stirlingFirst 0 k : ℚ) * x ^ k = 1 := by
  rw [Nat.sum_stirlingFirst_mul_pow]
  simp

/-- `n = 3`: `x (x + 1) (x + 2) = 2 x + 3 x² + x³`, read off the identity. -/
example (x : ℚ) : x * (x + 1) * (x + 2) = 2 * x + 3 * x ^ 2 + x ^ 3 := by
  have h := Nat.sum_stirlingFirst_mul_pow 3 x
  simp only [sum_range_succ, range_zero, sum_empty] at h
  simp only [ascPochhammer_succ_eval, ascPochhammer_zero, eval_one] at h
  norm_num [Nat.stirlingFirst] at h
  exact h.symm

/-- The row sum of the unsigned Stirling numbers of the first kind is `n!` (evaluate at `1`). -/
example (n : ℕ) : ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : ℕ) = n.factorial := by
  have h := Nat.sum_stirlingFirst_mul_pow n (1 : ℕ)
  simp only [one_pow, mul_one, Nat.cast_id] at h
  rw [h, ascPochhammer_nat_eq_ascFactorial, Nat.one_ascFactorial]

/-- The polynomial identity for `n = 2`: `X (X + 1) = X + X²`. -/
example : ∑ k ∈ range 3, (Nat.stirlingFirst 2 k : ℤ[X]) * X ^ k = X * (X + 1) := by
  rw [Nat.sum_stirlingFirst_mul_X_pow]
  simp [ascPochhammer_succ_right]

end MathlibExtTest.Combinatorics.Enumerative.StirlingAscPochhammer
