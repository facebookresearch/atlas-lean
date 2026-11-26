/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CountingAppearancesProgressionsAvailableCountDistinctPrimes

/-! # Tests for available integers for distinct primes -/

namespace MathlibExtTest.NumberTheory.CountingAppearancesProgressionsAvailableCountDistinctPrimes

open MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

-- For 2, 3 and 5 with zero residues, direct evaluation gives 22 available integers.
example : availableCount ![2, 3, 5] ![0, 0, 0] = 22 := by decide

-- Residues may exceed their moduli; the count is still 22.
example : availableCount ![2, 3, 5] ![100, 200, 300] = 22 := by decide

-- The theorem gives the determinant 22 for every choice of residues.
example (r : Fin 3 → ℕ) : (availableCount ![2, 3, 5] r : ℤ) = 22 := by
  have hprime : ∀ i, ((![2, 3, 5] : Fin 3 → ℕ) i).Prime := by decide
  have hinj : Function.Injective (![2, 3, 5] : Fin 3 → ℕ) := by decide
  rw [availableCount_distinct_primes 3 (by decide) ![2, 3, 5] hprime hinj r]
  exact (Matrix.det_fin_three (R := ℤ)
    (fun i j => if i = j then (((![2, 3, 5] : Fin 3 → ℕ) i : ℕ) : ℤ) else 1)).trans
    (by decide)

end MathlibExtTest.NumberTheory.CountingAppearancesProgressionsAvailableCountDistinctPrimes
