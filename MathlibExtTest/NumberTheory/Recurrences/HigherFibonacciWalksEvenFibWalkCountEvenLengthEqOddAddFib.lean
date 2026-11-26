/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksEvenFibWalkCountEvenLengthEqOddAddFib
import Mathlib.Tactic.LinearCombination

/-! # Tests for even and odd parts of the Fibonacci self-convolution at even length -/

namespace MathlibExtTest.NumberTheory.Recurrences.HigherFibonacciWalksEvenFibWalkCountEvenLengthEqOddAddFib

open MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

-- Length two is the smallest length covered by the theorem.
example : evenFibWalkCount (2 * 1)
    = oddFibWalkCount (2 * 1) + fibQ (2 * ((1 : ℕ) : ℤ) + 2) :=
  evenFibWalkCount_even_length_eq_odd_add_fib 1 le_rfl

-- At length two the values are 4, 1 and 3.
example : evenFibWalkCount 2 = 4 ∧ oddFibWalkCount 2 = 1 ∧ fibQ 4 = 3 := by
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · decide +kernel

-- The difference of the two parts is the Fibonacci number.
example (k : ℕ) (hk : 1 ≤ k) :
    evenFibWalkCount (2 * k) - oddFibWalkCount (2 * k)
      = fibQ (2 * (k : ℤ) + 2) := by
  have h := evenFibWalkCount_even_length_eq_odd_add_fib k hk
  linear_combination h

-- Length four unfolds to 14, 6 and 8.
example : evenFibWalkCount 4 = oddFibWalkCount 4 + fibQ 6 := by
  have h := evenFibWalkCount_even_length_eq_odd_add_fib 2 (by decide)
  simpa using h

end MathlibExtTest.NumberTheory.Recurrences.HigherFibonacciWalksEvenFibWalkCountEvenLengthEqOddAddFib
