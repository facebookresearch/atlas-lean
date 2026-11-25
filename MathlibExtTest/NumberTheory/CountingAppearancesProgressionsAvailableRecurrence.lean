/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CountingAppearancesProgressionsAvailableRecurrence
import Mathlib.Data.Nat.Prime.Nth

/-! # Tests for the recurrence for available integers modulo the first primes -/

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

-- At the lower boundary, the first two primes leave five available integers.
example : availableCount (firstPrimes 2) ![0, 0] = 5 := by
  have h₁ : firstPrimes 1 = ![2] := by
    funext i
    fin_cases i
    exact Nat.nth_prime_zero_eq_two
  rw [availableCount_firstPrimes_succ 1 (by decide), Nat.nth_prime_one_eq_three, h₁]
  decide

-- Noncanonical residues modulo 2, 3 and 5. The prefix has five available and two free integers.
example : availableCount (firstPrimes 3) ![3, 5, 12] = 22 := by
  have h₂ : firstPrimes 2 = ![2, 3] := by
    funext i
    fin_cases i <;> simp [firstPrimes, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  have hr : (![3, 5, 12] ∘ Fin.castSucc : Fin 2 → ℕ) = ![3, 5] := by
    funext i
    fin_cases i <;> rfl
  rw [availableCount_firstPrimes_succ 2 (by decide), Nat.nth_prime_two_eq_five, h₂, hr]
  decide

-- Check the same nontrivial count directly, without the recurrence.
example : availableCount ![2, 3, 5] ![3, 5, 12] = 22 := by decide

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
