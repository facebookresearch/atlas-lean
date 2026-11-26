/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CountingAppearancesProgressionsFirstPrimes
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic.NormNum

/-! # Tests for free integers and bordered determinants for the first primes -/

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

-- The empty product gives the one-element interval {1}.
example (r : Fin 0 → ℕ) : borderedOnesDiagDet (firstPrimes 0) = 1 := by
  rw [← freeCount_firstPrimes 0 r]
  simp [freeCount, residueHitCount]

-- These noncanonical residues leave eight integers, including the endpoint 30.
example : borderedOnesDiagDet (firstPrimes 3) = 8 := by
  have h : firstPrimes 3 = ![2, 3, 5] := by
    funext i
    fin_cases i <;>
      simp [firstPrimes, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
        Nat.nth_prime_two_eq_five]
  rw [← freeCount_firstPrimes 3 ![3, 5, 12], h]
  decide

-- At the first allowed index, the new factor is 3 - 1.
example : borderedOnesDiagDet (firstPrimes 2) = 2 * borderedOnesDiagDet (firstPrimes 1) := by
  have h := borderedOnesDiagDet_firstPrimes_recurrence 2 (by decide)
  norm_num [Nat.nth_prime_one_eq_three] at h
  exact h

-- The next step multiplies the previous determinant by 5 - 1.
example : borderedOnesDiagDet (firstPrimes 3) = 4 * borderedOnesDiagDet (firstPrimes 2) := by
  have h := borderedOnesDiagDet_firstPrimes_recurrence 3 (by decide)
  norm_num [Nat.nth_prime_two_eq_five] at h
  exact h

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
