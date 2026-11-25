/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FibonacciSquaredWeightedSum

/-! # Tests for the weighted sums of squared Fibonacci numbers -/

namespace MathlibExtTest.FibonacciSquaredWeightedSum

open Finset MetaMathlibExt

-- At the lower endpoint the parity correction is zero and each sum has one term.
example : (∑ k ∈ Icc 1 (1 : ℕ), ((1 - k + 1 : ℕ) : ℤ) * (Nat.fib k : ℤ) ^ 2) = 1 ∧
    (∑ k ∈ Icc 1 (1 : ℕ), (k : ℤ) * (Nat.fib (1 - k + 1) : ℤ) ^ 2) = 1 := by
  obtain ⟨h₁, h₂⟩ := fib_succ_sq_sub_parity_eq_sum (n := 1) le_rfl
  exact ⟨h₁.symm, h₂.symm⟩

-- At n = 4 the first sum is 4 + 3 + 8 + 9, and the second has those terms in reverse order.
example : (Nat.fib 5 : ℤ) ^ 2 - (5 % 2 : ℕ) = 24 ∧
    (∑ k ∈ Icc 1 (4 : ℕ), ((4 - k + 1 : ℕ) : ℤ) * (Nat.fib k : ℤ) ^ 2) = 24 ∧
    (∑ k ∈ Icc 1 (4 : ℕ), (k : ℤ) * (Nat.fib (4 - k + 1) : ℤ) ^ 2) = 24 := by
  decide

end MathlibExtTest.FibonacciSquaredWeightedSum
