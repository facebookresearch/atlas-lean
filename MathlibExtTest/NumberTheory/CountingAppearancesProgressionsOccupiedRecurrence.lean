/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Prime.Nth
import MathlibExt.NumberTheory.CountingAppearancesProgressionsOccupiedRecurrence

/-! # Tests for the recurrence for occupied integers modulo the first primes -/

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

-- There are no occupied integers for one prime, and one for the first two primes.
example : occupiedCount ![2] ![0] = 0 ∧ occupiedCount ![2, 3] ![0, 0] = 1 := by decide

-- With noncanonical residues modulo 2, 3, and 5, the recurrence gives eight occupied integers.
example : occupiedCount (firstPrimes 3) ![3, 5, 12] = 8 := by
  have hp : firstPrimes 2 = ![2, 3] := by
    funext i
    fin_cases i <;> simp [firstPrimes, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  have hr : (![3, 5, 12] ∘ Fin.castSucc : Fin 2 → ℕ) = ![3, 5] := by
    funext i
    fin_cases i <;> rfl
  have h := occupiedCount_firstPrimes_succ_add_free 2 (by decide) ![3, 5, 12]
  change occupiedCount (firstPrimes 3) ![3, 5, 12] + freeCount (firstPrimes 2) _ =
    (∏ i, firstPrimes 2 i) + (Nat.nth Nat.Prime 2 - 1) * occupiedCount (firstPrimes 2) _ at h
  rw [hp, hr, Nat.nth_prime_two_eq_five] at h
  have hfree : freeCount ![2, 3] ![3, 5] = 2 := by decide
  have hocc : occupiedCount ![2, 3] ![3, 5] = 1 := by decide
  have hprod : (∏ i, (![2, 3] : Fin 2 → ℕ) i) = 6 := by decide
  rw [hfree, hocc, hprod] at h
  omega

-- Independently enumerate the occupied integers for the same residues.
example : occupiedCount ![2, 3, 5] ![3, 5, 12] = 8 := by decide

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
