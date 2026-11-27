/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CountingAppearancesProgressionsFirstPrimes
import Mathlib.Data.Nat.Prime.Nth

/-! # Tests for free integers modulo the first primes -/

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

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
