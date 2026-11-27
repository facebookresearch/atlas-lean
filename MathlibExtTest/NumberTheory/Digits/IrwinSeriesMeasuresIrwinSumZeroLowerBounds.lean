/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresIrwinSumZeroLowerBounds
import Mathlib.Tactic.NormNum

/-!
# Tests for the lower bounds for the Irwin sum without a nonzero digit

These tests specialize the logarithmic bounds to decimal digit exclusion.

Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Proposition 2.
-/

namespace MathlibExtTest.NumberTheory.Digits.IrwinSeriesMeasuresIrwinSumZeroLowerBounds

open MetaMathlibExt

example : (10 : ℝ) * Real.log 5 < irwinSum 10 9 0 := by
  simpa only [Nat.cast_ofNat, show (10 : ℝ) / 2 = 5 by norm_num] using
    (irwinSum_zero_lowerBounds 10 9 (by decide) (by decide) (by decide)).2

example : (10 : ℝ) * Real.log 10 - 10 * Real.log (10 / 9 : ℝ) < irwinSum 10 9 0 := by
  convert (irwinSum_zero_lowerBounds 10 9 (by decide) (by decide) (by decide)).1 using 1
  norm_num

end MathlibExtTest.NumberTheory.Digits.IrwinSeriesMeasuresIrwinSumZeroLowerBounds
