/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasures
import Mathlib.Tactic.NormNum

open MetaMathlibExt MeasureTheory

-- Numerals use minimal representations, while digit strings retain leading zeroes.
example : digitCount 10 0 100 = 2 := by decide

example : normalizedStringValue 10 [0, 3] = 3 / 100 := by
  norm_num [normalizedStringValue, stringValue, List.foldl]

example (b : ℕ) : stringAtom b [] = Measure.dirac (0 : ℝ) := stringAtom_nil b

-- A prefix longer than the whole numeral keeps the numeral, by truncated subtraction.
example : leadingDigits 10 4 73 = 73 := by decide
