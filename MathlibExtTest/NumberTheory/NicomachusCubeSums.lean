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
