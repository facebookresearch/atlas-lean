/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativePrimeThreeModFour
import Mathlib.Tactic.NormNum

/-!
# Tests for parallelogram induction at primes congruent to three modulo four

The prime-induction theorem gives the square values at 19 and 31.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 6.
-/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction
namespace ParallelogramSquareUniquenessParallelogramMultiplicativePrimeThreeModFour

example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (hind : ∀ q s : ℕ, q.Prime → q < 19 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 19 = 361 := by
  convert MetaMathlibExt.parallelogram_multiplicative_prime_three_mod_four f hf hpar
    (p := 19) (by decide) hind (k := 5) (by decide) (by decide) using 1
  norm_num

example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (hind : ∀ q s : ℕ, q.Prime → q < 31 → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s)) :
    f 31 = 961 := by
  convert MetaMathlibExt.parallelogram_multiplicative_prime_three_mod_four f hf hpar
    (p := 31) (by decide) hind (k := 8) (by decide) (by decide) using 1
  norm_num

end ParallelogramSquareUniquenessParallelogramMultiplicativePrimeThreeModFour
end MathlibExtTest.NumberTheory.ArithmeticFunction
