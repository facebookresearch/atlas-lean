/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomialFibonacciConvolution

/-! # Tests for binomial sums of Fibonacci numbers -/

open MetaMathlibExt Finset

/-- The shifted binomial identity `∑ binom(n, i) F_{i+m} = F_{2n+m}` at
`n = 4`, `m = 3`. -/
example : ∑ i ∈ range 5, (4 : ℕ).choose i * Nat.fib (i + 3) = 89 := by
  rw [Nat.sum_range_choose_mul_fib_add]
  decide

example : ∑ i ∈ range 5, (4 : ℕ).choose i * Nat.fib (i + 3) =
    Nat.fib (2 * 4 + 3) := by
  decide

#print axioms Nat.sum_range_choose_mul_fib_add
