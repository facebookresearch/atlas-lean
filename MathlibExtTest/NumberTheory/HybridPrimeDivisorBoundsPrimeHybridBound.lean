/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HybridPrimeDivisorBoundsPrimeHybridBound
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import MathlibExt.NumberTheory.Cyclotomic.CommonPrimeDivisorEvalPow
import MathlibExt.NumberTheory.Cyclotomic.ComposedFactorization
import MathlibExt.NumberTheory.Cyclotomic.PrimeDivisorCongruence
import MathlibExt.NumberTheory.Cyclotomic.PrimePowerDivisibility
import MathlibExt.NumberTheory.Cyclotomic.TwoPowRamifiedBound

/-! # Tests for the `p`-hybrid bound -/

namespace MathlibExtTest.NumberTheory.HybridPrimeDivisorBoundsPrimeHybridBound

-- p = 3, x = 4: 4^3 - 1 = 63 = 3^2 * 7, so ω = 2 and k < 2.
example : ∃ k < 2,
    (∀ i < k, 0 < Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 3 ρ 1) i) ∧
    1 + ∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 3 ρ 1) i ≤ 4 ∧
      1 + (∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 3 ρ 1) i) *
          ∏ j ∈ Finset.range (2 - k),
            Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq 3 ρ 1) j ≤ 4 ^ 3 := by
  have h63 : ((4 ^ 3 - 1).primeFactors.card = 2) := by
    have h41 : (4 ^ 3 - 1 : ℕ) = 63 := by decide
    rw [h41]
    have h63e : (63 : ℕ) = 3 ^ 2 * 7 := by decide
    rw [h63e, Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_pow _ (by decide),
      Nat.prime_three.primeFactors, Nat.prime_seven.primeFactors]
    decide
  have h := MetaMathlibExt.prime_hybrid_bound Nat.prime_three (by decide : 1 < 4)
  rw [h63] at h
  exact h

-- p = 2, x = 5: 5^2 - 1 = 24 = 2^3 * 3, so ω = 2 and k < 2.
example : ∃ k < 2,
    (∀ i < k, 0 < Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 2 ρ 1) i) ∧
    1 + ∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 2 ρ 1) i ≤ 5 ∧
      1 + (∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 2 ρ 1) i) *
          ∏ j ∈ Finset.range (2 - k),
            Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq 2 ρ 1) j ≤ 5 ^ 2 := by
  have h24 : ((5 ^ 2 - 1).primeFactors.card = 2) := by
    have h51 : (5 ^ 2 - 1 : ℕ) = 24 := by decide
    rw [h51]
    have h24e : (24 : ℕ) = 2 ^ 3 * 3 := by decide
    rw [h24e, Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_pow _ (by decide),
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
    decide
  have h := MetaMathlibExt.prime_hybrid_bound Nat.prime_two (by decide : 1 < 5)
  rw [h24] at h
  exact h

-- p = 2, x = 3: 3^2 - 1 = 8 = 2^3, so ω = 1 and k = 0.
example : ∃ k < 1,
    (∀ i < k, 0 < Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 2 ρ 1) i) ∧
    1 + ∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 2 ρ 1) i ≤ 3 ∧
      1 + (∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 2 ρ 1) i) *
          ∏ j ∈ Finset.range (1 - k),
            Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq 2 ρ 1) j ≤ 3 ^ 2 := by
  have h8 : ((3 ^ 2 - 1).primeFactors.card = 1) := by
    have h31 : (3 ^ 2 - 1 : ℕ) = 8 := by decide
    rw [h31]
    have h8e : (8 : ℕ) = 2 ^ 3 := by decide
    rw [h8e, Nat.primeFactors_pow _ (by decide), Nat.prime_two.primeFactors]
    decide
  have h := MetaMathlibExt.prime_hybrid_bound Nat.prime_two (by decide : 1 < 3)
  rw [h8] at h
  exact h

end MathlibExtTest.NumberTheory.HybridPrimeDivisorBoundsPrimeHybridBound
