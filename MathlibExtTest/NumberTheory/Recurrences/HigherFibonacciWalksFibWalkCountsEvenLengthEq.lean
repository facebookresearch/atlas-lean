/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksFibWalkCountsEvenLengthEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for halving the Fibonacci self-convolution

These tests specialize the even-length formula and derive the difference of its two parts.
-/

set_option autoImplicit false

namespace MathlibExtTest.NumberTheory.Recurrences.HigherFibonacciWalksFibWalkCountsEvenLengthEq

open MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

example : evenFibWalkCount 2 = 4 ∧ oddFibWalkCount 2 = 1 := by
  convert fibWalkCounts_even_length_eq 1 (by decide) using 1 <;>
    norm_num [fibWalkCount, Finset.sum_range_succ, fibQ, Int.fib, Nat.fib]

example (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k) - oddFibWalkCount (2 * k) = fibQ (2 * (k : ℤ) + 2) := by
  obtain ⟨he, ho⟩ := fibWalkCounts_even_length_eq k hk
  rw [he, ho]
  ring

end MathlibExtTest.NumberTheory.Recurrences.HigherFibonacciWalksFibWalkCountsEvenLengthEq
