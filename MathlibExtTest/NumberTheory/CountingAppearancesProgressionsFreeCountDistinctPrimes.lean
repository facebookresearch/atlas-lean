/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CountingAppearancesProgressionsAvailableCountDistinctPrimes

/-! # Tests for free integers modulo distinct primes -/

namespace MathlibExtTest.NumberTheory.CountingAppearancesProgressionsFreeCountDistinctPrimes

open MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

-- The free integers are 2 and 6; in particular, the period's right endpoint is counted.
example : (Finset.Icc 1 6).filter
    (fun n => residueHitCount ![3, 2] ![1, 1] n = 0) = {2, 6} := by decide

example : freeCount ![3, 2] ![1, 1] = 2 := by decide

example : borderedOnesDiagDet ![3, 2] = 2 := by decide

-- Unsorted primes and unreduced residues; the odd number of primes tests the negative sign.
example : freeCount ![7, 2, 5] ![15, 8, 12] = 24 := by decide

example : borderedOnesDiagDet ![7, 2, 5] = 24 := by decide

-- Moving the border to the bottom gives the symmetric matrix determinant.
example : (Matrix.of (fun i j : Fin 4 =>
    if i = j then ((Fin.snoc ![7, 2, 5] 1 : Fin 4 → ℕ) i : ℤ) else 1)).det = 24 := by decide

-- Client example with a different residue choice from the independent two-prime check.
example : (freeCount ![3, 2] ![7, 4] : ℤ) = 2 := by
  rw [freeCount_distinct_primes 2 (by decide) ![3, 2] (by decide) (by decide) ![7, 4]]
  decide

end MathlibExtTest.NumberTheory.CountingAppearancesProgressionsFreeCountDistinctPrimes
