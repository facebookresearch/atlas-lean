/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.KFoldDivisor

/-!
# Tests for the Piltz divisor functions
-/

@[expose] public section

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

/-! ### Concrete values -/

example : piltz 2 6 = 4 := by decide
example : piltz 3 4 = 6 := by decide
example : piltz 3 12 = 18 := by decide
example : piltz 1 7 = 1 := by decide
example : piltzNontrivial 2 6 = 2 := by decide
example : piltzNontrivial 2 4 = 1 := by decide
example : piltzNontrivial 3 8 = 1 := by decide
example : piltzNontrivial 3 12 = 3 := by decide

/-! ### Boundary values -/

-- `d_k(0) = 0` for every `k`, and `d_0` is the Dirichlet unit.
example (k : ℕ) : piltz k 0 = 0 := by simp
example : piltz 0 1 = 1 := by simp
example (n : ℕ) (hn : n ≠ 1) : piltz 0 n = 0 := by simp [hn]
example (n : ℕ) (hn : n ≠ 0) : piltz 1 n = 1 := by simp [hn]
-- `d_k^*(1) = 0` for `k ≥ 1` (there is no factor `≥ 2`), but `d_0^*(1) = 1`.
example : piltzNontrivial 0 1 = 1 := by decide
example : piltzNontrivial 1 1 = 0 := by decide
example : piltzNontrivial 2 1 = 0 := by decide
-- `d_1^* = ζ - δ`, read off from `d_k^* = (ζ - 1) ^ k`.
example : piltzNontrivial 1 5 = 1 := by decide
example (n : ℕ) :
    (piltzNontrivial 1 n : ℤ) = ((ζ : ArithmeticFunction ℤ) - 1) n := by
  simpa using congrArg (fun f : ArithmeticFunction ℤ => f n) (piltzNontrivial_eq_zeta_sub_one_pow 1)

/-! ### Agreement with Mathlib's objects -/

example (n : ℕ) : piltz 2 n = (n.divisors.card) := by
  simp [sigma_zero_apply]

example (k : ℕ) : piltz k = (ζ : ArithmeticFunction ℕ) ^ k := piltz_eq_zeta_pow k

example (n : ℕ) : piltz 3 n = ∑ d ∈ n.divisors, (σ 0 d) := by
  simp [piltz_succ_apply]

-- The general Dirichlet-power formula, for `f = id` and `k = 2`: `(id * id)(n) = n σ₀(n)`.
example : ((ArithmeticFunction.id : ArithmeticFunction ℕ) ^ 2) 6 = 24 := by
  rw [pow_apply_eq_sum_finMulAntidiag]
  decide

example {k n : ℕ} (hk : k ≠ 0) (hn : n ≠ 0) : 0 < piltz k n := piltz_pos hk hn
example : piltz 2 12 ≤ piltz 3 12 := piltz_le_piltz_succ 2 12

-- `piltz_le_piltz_succ` holds at `n = 0`, where both sides vanish.
example (k : ℕ) : piltz k 0 ≤ piltz (k + 1) 0 := piltz_le_piltz_succ k 0
