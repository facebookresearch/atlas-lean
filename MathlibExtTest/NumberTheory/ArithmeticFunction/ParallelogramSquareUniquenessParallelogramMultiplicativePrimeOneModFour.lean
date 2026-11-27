/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativePrimeOneModFour
import Mathlib.Tactic.NormNum

/-!
# Parallelogram induction at the prime five

Specializing the induction theorem to five requires square values only at powers of two
and three and gives `f 5 = 25`.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 5.
-/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction

namespace ParallelogramSquareUniquenessParallelogramMultiplicativePrimeOneModFour

example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (htwo : ∀ s : ℕ, 1 ≤ s → f (2 ^ s) = (2 : ℂ) ^ (2 * s))
    (hthree : ∀ s : ℕ, 1 ≤ s → f (3 ^ s) = (3 : ℂ) ^ (2 * s)) : f 5 = 25 := by
  have hind (q s : ℕ) (hq : q.Prime) (hlt : q < 5) (hs : 1 ≤ s) :
      f (q ^ s) = (q : ℂ) ^ (2 * s) := by
    have hq4 : q ≠ 4 := by
      rintro rfl
      exact (by decide : ¬ Nat.Prime 4) hq
    have hq23 : q = 2 ∨ q = 3 := by
      have := hq.two_le
      omega
    rcases hq23 with rfl | rfl
    · exact htwo s hs
    · exact hthree s hs
  have hfive : ((5 : ℕ) : ℂ) ^ 2 = 25 := by norm_num
  simpa only [hfive] using MetaMathlibExt.parallelogram_multiplicative_prime_one_mod_four f hf hpar
    (p := 5) (by decide) hind (by decide)

end ParallelogramSquareUniquenessParallelogramMultiplicativePrimeOneModFour

end MathlibExtTest.NumberTheory.ArithmeticFunction
