/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitTotientFormula
import Mathlib.Data.Nat.Prime.Defs

namespace MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitTotientFormula

-- At the prime `2`, the totient value is `2 - 1 = 1`.
example (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ MetaMathlibExt.squareSplitDivisors n, φ d = n) :
    φ 2 = 1 := by
  obtain ⟨-, -, hpp, -⟩ := MetaMathlibExt.squareSplitTotient_formula φ hφ
  have h2 := (hpp 2 Nat.prime_two).1
  omega

-- At `4 = 2 ^ 2`, the totient value is `(2 ^ 2 - 1) * 2 ^ 0 = 3`.
example (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ MetaMathlibExt.squareSplitDivisors n, φ d = n) :
    φ 4 = 3 := by
  obtain ⟨-, -, hpp, -⟩ := MetaMathlibExt.squareSplitTotient_formula φ hφ
  have h4 := ((hpp 2 Nat.prime_two).2 1 le_rfl).1
  have e : (2 : ℕ) ^ (2 * 1) = 4 := by decide
  have e2 : ((((2 : ℕ) : ℤ) ^ 2 - 1) * ((2 : ℕ) : ℤ) ^ (2 * 1 - 2)) = 3 := by decide
  rw [e, e2] at h4
  exact h4

-- Multiplicativity gives `φ 6 = φ 2 * φ 3 = 1 * 2 = 2`.
example (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ MetaMathlibExt.squareSplitDivisors n, φ d = n) :
    φ 6 = 2 := by
  obtain ⟨hmult, -, hpp, -⟩ := MetaMathlibExt.squareSplitTotient_formula φ hφ
  have h6 : φ (2 * 3) = φ 2 * φ 3 :=
    hmult.map_mul_of_coprime (show Nat.gcd 2 3 = 1 from by decide)
  have h2 := (hpp 2 Nat.prime_two).1
  have h3 := (hpp 3 Nat.prime_three).1
  have e6 : (2 : ℕ) * 3 = 6 := by decide
  have e23 : (((2 : ℕ) : ℤ) - 1) * (((3 : ℕ) : ℤ) - 1) = 2 := by decide
  rw [e6, h2, h3, e23] at h6
  exact h6

-- The product formula at `1` recovers `(φ 1 : ℚ) = 1`.
example (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ MetaMathlibExt.squareSplitDivisors n, φ d = n) :
    (φ 1 : ℚ) = 1 := by
  obtain ⟨-, -, -, hform⟩ := MetaMathlibExt.squareSplitTotient_formula φ hφ
  have h := hform 1 one_ne_zero
  rw [MetaMathlibExt.squareSplitU_one, MetaMathlibExt.squareSplitV_one, Nat.totient_one,
    Nat.primeFactors_one, Finset.prod_empty, Nat.cast_one, one_pow, mul_one, mul_one] at h
  exact h

end MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitTotientFormula
