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
example : (7 : ℤ) ∣ lehmerV 2 (-1) 4 := by
  exact mersenne_dvd_lehmerV_of_diophantine (n := 3) (by decide) (by decide)
    (by decide) 2 6 (-1) 1 1 1 (by decide) (by decide)
    (by norm_num [mersenne]) (by norm_num [mersenne])

-- The positive `Q = 3` example at exponent 5 uses the sixteenth term.
example : (31 : ℤ) ∣ lehmerV 8 3 16 := by
  exact mersenne_dvd_lehmerV_of_diophantine (n := 5) (by decide) (by decide)
    (by decide) 2 (-1) 3 2 1 2 (by decide) (by decide)
    (by norm_num [mersenne]) (by norm_num [mersenne])
