/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
import MathlibExt.NumberTheory.LehmerCompanionMersenneDivisibility

/-! # Tests for Lehmer companion divisibility by a Mersenne prime -/

open MetaMathlibExt

-- An odd-index term tests the companion recurrence beyond its four initial values.
example : lehmerV 8 3 5 = -11 := by decide

-- At the smallest permitted exponent, the parameters give the fourth term with `Q = -1`.
example : lehmerV 2 (-1) 4 % 7 = 0 := by decide

-- Check the two symbols and the companion remainder independently for positive `Q` at `n = 5`.
example : jacobiSym ((8 - 4 * 3) * 8) (mersenne 5) = -1 ∧
    jacobiSym (3 * 8) (mersenne 5) = -1 ∧ lehmerV 8 3 16 % 31 = 0 := by
  refine ⟨?_, ?_, by decide⟩ <;> norm_num [mersenne]

-- Scaling the smallest-exponent example gives noncoprime parameters `R = 4` and `Q = -2`.
example : jacobiSym ((4 - 4 * (-2)) * 4) (mersenne 3) = -1 ∧
    jacobiSym ((-2) * 4) (mersenne 3) = -1 ∧ lehmerV 4 (-2) 4 % 7 = 0 := by
  refine ⟨?_, ?_, by decide⟩ <;> norm_num [mersenne]

example : (7 : ℤ) ∣ lehmerV 4 (-2) 4 := by
  exact mersenne_dvd_lehmerV_of_jacobi (n := 3) (by decide) (by decide) (by decide) 4 (-2)
    (by norm_num [mersenne]) (by norm_num [mersenne])
