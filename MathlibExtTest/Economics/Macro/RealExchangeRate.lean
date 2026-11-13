/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.RealExchangeRate

import Mathlib.Tactic

/-!
# Tests for the real exchange rate

`E = 1.2, P* = 100, P = 120` gives `q = 1` (a PPP example);
`E = 1.5, P* = 100, P = 120` gives `q = 5 / 4` (non-PPP, so the test is
not PPP-only).
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.RealExchangeRate

open MathlibExt.Economics.Macro.RealExchangeRate

-- Test section: concrete examples with exact values.
/-- PPP example: `E = 1.2, P* = 100, P = 120` gives `q = 1`. -/
example : realExchangeRate 1.2 100 120 = 1 := by
  unfold realExchangeRate
  norm_num

/-- Conversion identity for the PPP example: `1 * 120 = 1.2 * 100`. -/
example : (1 : ℝ) * 120 = 1.2 * 100 := by
  norm_num

/-- Conversion identity via the pinned theorem (PPP values). -/
example : realExchangeRate 1.2 100 120 * 120 = 1.2 * 100 :=
  realExchangeRate_mul_price 1.2 100 120 (by norm_num)

/-- NON-PPP example (required so the test is not PPP-only):
`E = 1.5, P* = 100, P = 120` gives `q = 5 / 4`. -/
example : realExchangeRate 1.5 100 120 = 5 / 4 := by
  unfold realExchangeRate
  norm_num

/-- Conversion identity via the pinned theorem (NON-PPP values). -/
example : realExchangeRate 1.5 100 120 * 120 = 1.5 * 100 :=
  realExchangeRate_mul_price 1.5 100 120 (by norm_num)

/-- Price-ratio form at NON-PPP values, via the pinned theorem. -/
example : realExchangeRate 1.5 100 120 = 1.5 / (120 / 100) :=
  realExchangeRate_eq_nominal_div_priceRatio 1.5 100 120 (by norm_num) (by norm_num)

/-- Strict monotonicity in the nominal rate at exact values:
`E = 1.2` vs `E = 1.5` (with `P* = 100, P = 120`), via the pinned theorem. -/
example : realExchangeRate 1.2 100 120 < realExchangeRate 1.5 100 120 :=
  realExchangeRate_strictMono_nominal 100 120 (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.Economics.Macro.RealExchangeRate
