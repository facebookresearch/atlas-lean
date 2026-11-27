/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NicomachusCubeSums
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.NicomachusGeneralizationWanted

-- At the first admissible index the even polynomial uses the reflected argument -3.
example : nicomachusLEven 2 1 - nicomachusREven 2 1 = 76 := by
  rw [nicomachusLEven_sub_REven_eq 2 (hm := le_rfl)]
  norm_num [nicomachusPEven, nicomachusPClosed]

-- At x = 0 the polynomial correction vanishes, recovering the classical identity.
example (m : ℕ) (hm : 2 ≤ m) : nicomachusLEven m 0 = nicomachusTriangular (2 * m) ^ 2 := by
  simpa [nicomachusREven, sub_eq_zero] using nicomachusLEven_sub_REven_eq m hm 0

-- At x = -2 each term of the second sum is zero, leaving the odd cubes and x³.
example : nicomachusLEven 2 (-2) = 20 := by
  norm_num [nicomachusLEven, show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_insert]

-- Compute the first admissible odd case directly from the two cube sums and the square.
example : nicomachusLOdd 3 1 - nicomachusROdd 3 1 = 36 := by
  norm_num [nicomachusLOdd, nicomachusROdd, nicomachusTriangular,
    show Finset.Icc 1 3 = {1, 2, 3} by decide, show Finset.Icc 2 3 = {2, 3} by decide,
    Finset.sum_insert]

-- Apply the odd theorem beyond the base case, where the left index is one greater.
example : nicomachusLOdd 4 (-1) - nicomachusROdd 4 (-1) = 90 := by
  rw [nicomachusLOdd_sub_ROdd_succ_eq 3 (by decide)]
  norm_num [nicomachusPOdd, show Finset.Icc 0 3 = {0, 1, 2, 3} by decide, Finset.sum_insert]

-- The zero correction recovers the odd-termination form of the classical identity.
example (m : ℕ) (hm : 2 ≤ m) :
    nicomachusLOdd (m + 1) 0 = nicomachusTriangular (2 * (m + 1) - 1) ^ 2 := by
  simpa [nicomachusROdd, sub_eq_zero] using nicomachusLOdd_sub_ROdd_succ_eq m hm 0
