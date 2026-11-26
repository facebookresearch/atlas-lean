/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksOddLengthHalf

/-! # Tests for halving the Fibonacci self-convolution at odd length -/

namespace MathlibExtTest.NumberTheory.Recurrences.HigherFibonacciWalksOddLengthHalf

open MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

-- Length one is the smallest length covered by the theorem.
example : evenFibWalkCount 1 = fibWalkCount 1 / 2 ∧ oddFibWalkCount 1 = fibWalkCount 1 / 2 :=
  fibWalkCounts_odd_length_eq_half 1 le_rfl

-- Evaluate the three counts directly at the first two odd lengths.
example : evenFibWalkCount 1 = 1 ∧ oddFibWalkCount 1 = 1 ∧ fibWalkCount 1 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

example : evenFibWalkCount 3 = 5 ∧ oddFibWalkCount 3 = 5 ∧ fibWalkCount 3 = 10 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end MathlibExtTest.NumberTheory.Recurrences.HigherFibonacciWalksOddLengthHalf
