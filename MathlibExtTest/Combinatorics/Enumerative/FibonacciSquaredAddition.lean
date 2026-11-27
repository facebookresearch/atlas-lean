/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FibonacciSquaredAddition

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.FibonacciSquaredAddition` -/

namespace MathlibExtTest.FibonacciSquaredAddition

open Finset MetaMathlibExt

-- The smallest admissible indices `m = 1`, `n = 2`, with `n - 1` reduced: `F_3² = 1 + 1 + 2`.
example : Nat.fib (1 + 2) ^ 2 =
    Nat.fib 2 ^ 2 * Nat.fib 2 ^ 2 + Nat.fib 1 ^ 2 * Nat.fib 1 ^ 2 +
      2 * (∑ i ∈ Icc 1 1, Nat.fib i ^ 2) * ∑ j ∈ Icc 1 1, Nat.fib j ^ 2 :=
  fib_add_sq_eq le_rfl le_rfl

-- Both sides evaluated at `m = 3`, `n = 4`: `F_7² = 169 = 81 + 16 + 72`.
example : Nat.fib (3 + 4) ^ 2 = 169 := by decide

example : Nat.fib (3 + 1) ^ 2 * Nat.fib 4 ^ 2 + Nat.fib 3 ^ 2 * Nat.fib (4 - 1) ^ 2 +
    2 * (∑ i ∈ Icc 1 3, Nat.fib i ^ 2) * ∑ j ∈ Icc 1 (4 - 1), Nat.fib j ^ 2 = 169 := by
  decide

-- An independent check of the identity by evaluation, for `1 ≤ m ≤ 5` and `2 ≤ n ≤ 5`.
example : ∀ m ∈ Icc 1 5, ∀ n ∈ Icc 2 5,
    Nat.fib (m + n) ^ 2 =
      Nat.fib (m + 1) ^ 2 * Nat.fib n ^ 2 + Nat.fib m ^ 2 * Nat.fib (n - 1) ^ 2 +
        2 * (∑ i ∈ Icc 1 m, Nat.fib i ^ 2) * ∑ j ∈ Icc 1 (n - 1), Nat.fib j ^ 2 := by
  decide

-- The case `m = 1` in `simp` normal form: `F_(n+1)² = F_n² + F_(n-1)² + 2 ∑_{j=1}^{n-1} F_j²`.
example {n : ℕ} (hn : 2 ≤ n) :
    Nat.fib (n + 1) ^ 2 =
      Nat.fib n ^ 2 + Nat.fib (n - 1) ^ 2 + 2 * ∑ j ∈ Icc 1 (n - 1), Nat.fib j ^ 2 := by
  simpa [add_comm 1 n] using fib_add_sq_eq le_rfl hn

/-! ### `two_mul_sum_fib_sq` -/

-- The smallest admissible index `n = 3`: `2 F_1² = F_3² - F_2² - F_1²`, that is, `2 = 4 - 1 - 1`.
example : 2 * ∑ j ∈ Icc 1 (3 - 2), (Nat.fib j : ℤ) ^ 2 =
    (Nat.fib 3 : ℤ) ^ 2 - (Nat.fib (3 - 1) : ℤ) ^ 2 - (Nat.fib (3 - 2) : ℤ) ^ 2 :=
  two_mul_sum_fib_sq le_rfl

-- Both sides evaluated at `n = 7`: `2 (1 + 1 + 4 + 9 + 25) = 80 = 169 - 64 - 25`.
example : 2 * ∑ j ∈ Icc 1 (7 - 2), (Nat.fib j : ℤ) ^ 2 = 80 := by decide

example : (Nat.fib 7 : ℤ) ^ 2 - (Nat.fib (7 - 1) : ℤ) ^ 2 - (Nat.fib (7 - 2) : ℤ) ^ 2 = 80 := by
  decide

-- An independent check of the identity by evaluation, for `3 ≤ n ≤ 12`.
example : ∀ n ∈ Icc 3 12,
    2 * ∑ j ∈ Icc 1 (n - 2), (Nat.fib j : ℤ) ^ 2 =
      (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - 1) : ℤ) ^ 2 - (Nat.fib (n - 2) : ℤ) ^ 2 := by
  decide

-- The hypothesis `3 ≤ n` cannot be dropped: at `n = 1`, truncated subtraction makes the
-- right-hand side `F_1² - F_0² - F_0² = 1`, while the left-hand side is the empty sum `0`.
example : 2 * ∑ j ∈ Icc 1 (1 - 2), (Nat.fib j : ℤ) ^ 2 ≠
    (Nat.fib 1 : ℤ) ^ 2 - (Nat.fib (1 - 1) : ℤ) ^ 2 - (Nat.fib (1 - 2) : ℤ) ^ 2 := by
  decide

-- For `n = 0` and `n = 2`, the only other indices below `3`, both sides are `0`.
example : ∀ n ∈ ({0, 2} : Finset ℕ),
    2 * ∑ j ∈ Icc 1 (n - 2), (Nat.fib j : ℤ) ^ 2 = 0 ∧
      (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - 1) : ℤ) ^ 2 - (Nat.fib (n - 2) : ℤ) ^ 2 = 0 := by
  decide

end MathlibExtTest.FibonacciSquaredAddition
