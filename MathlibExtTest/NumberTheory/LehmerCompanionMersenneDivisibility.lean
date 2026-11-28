/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LehmerCompanionMersenneDivisibility

/-! # Tests for Lehmer companion divisibility by a Mersenne prime -/

open MetaMathlibExt

-- An odd-index term tests the companion recurrence beyond its four initial values.
example : lehmerV 8 3 5 = -11 := by decide

-- At the smallest permitted exponent, the parameters give the fourth term with `Q = -1`.
example : lehmerV 2 (-1) 4 % 7 = 0 := by decide

-- The positive `Q = 3` example at exponent 5 uses the sixteenth term.
example : lehmerV 8 3 16 % 31 = 0 := by decide
