/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CountingAppearancesProgressionsAvailableFirstPrimes

/-! # Tests for the available count modulo the first primes -/

namespace MathlibExtTest.NumberTheory.CountingAppearancesProgressionsAvailableFirstPrimes

open MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

private theorem firstPrimes_one : firstPrimes 1 = ![2] := by
  funext i
  fin_cases i
  exact firstPrimes_eq_iff.mpr (by decide)

private theorem firstPrimes_two : firstPrimes 2 = ![2, 3] := by
  funext i
  fin_cases i <;> exact firstPrimes_eq_iff.mpr (by decide)

-- The empty product is 1, so the interval contains only 1, with no hits.
example : availableCount (firstPrimes 0) ![] = 1 := by
  rw [availableCount_eq_card_filter]
  simp

example : onesDiagDet (firstPrimes 0) = 1 := by
  rw [onesDiagDet_eq_det_diagonal_add, Matrix.det_isEmpty]

-- For the single prime 2, both integers are available regardless of the single residue.
example : availableCount (firstPrimes 1) ![3] = 2 := by
  rw [firstPrimes_one, availableCount_eq_card_filter]
  decide

example : onesDiagDet (firstPrimes 1) = 2 := by
  rw [firstPrimes_one, onesDiagDet_eq_det_diagonal_add, Matrix.det_fin_one]
  decide

-- The residues 3 and 8 are noncanonical; 5 is the only double hit in [1, 6].
example : availableCount (firstPrimes 2) ![3, 8] = 5 := by
  rw [firstPrimes_two, availableCount_eq_card_filter]
  decide

example : onesDiagDet (firstPrimes 2) = 5 := by
  rw [firstPrimes_two, onesDiagDet_eq_det_diagonal_add, Matrix.det_fin_two]
  decide

-- Client example: the determinant also evaluates the count for a different choice of residues.
example : (availableCount (firstPrimes 2) ![0, 0] : ℤ) = 5 := by
  rw [availableCount_firstPrimes, firstPrimes_two, onesDiagDet_eq_det_diagonal_add, Matrix.det_fin_two]
  decide

end MathlibExtTest.NumberTheory.CountingAppearancesProgressionsAvailableFirstPrimes
