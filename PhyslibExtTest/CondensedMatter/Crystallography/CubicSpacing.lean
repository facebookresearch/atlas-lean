/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.CondensedMatter.Crystallography.CubicSpacing

/-!
# Cubic spacing formula checks

Concrete consumers of `PhyslibExt.CondensedMatter.Crystallography.CubicSpacing`: the expression
`a / √(h ^ 2 + k ^ 2 + l ^ 2)` at `a = 0.4` for the index patterns `(100)`,
`(110)`, `(111)`, and `(200)`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric values
- B. Index pattern `(200)`

## iv. References

- `PhyslibExt.CondensedMatter.Crystallography.CubicSpacing`
-/

/-- Numeric value: `(100)` gives `a`. -/
example : (0.4 : ℝ) / Real.sqrt ((1 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2) = 0.4 :=
  Crystallography.div_sqrt_sumSq_100

/-- Numeric value: `(110)` gives `a / √2`. -/
example : (0.4 : ℝ) / Real.sqrt ((1 : ℝ) ^ 2 + 1 ^ 2 + 0 ^ 2)
    = 0.4 / Real.sqrt 2 :=
  Crystallography.div_sqrt_sumSq_110

/-- Numeric value: `(111)` gives `a / √3`. -/
example : (0.4 : ℝ) / Real.sqrt ((1 : ℝ) ^ 2 + 1 ^ 2 + 1 ^ 2)
    = 0.4 / Real.sqrt 3 :=
  Crystallography.div_sqrt_sumSq_111

/-- Numeric value: `(200)` gives exactly `a / 2 = 0.4 / 2`, from the squared
identity and positivity of both sides. -/
example : (0.4 : ℝ) / Real.sqrt (((2 : ℤ) : ℝ) ^ 2 + ((0 : ℤ) : ℝ) ^ 2 + ((0 : ℤ) : ℝ) ^ 2)
    = 0.4 / 2 := by
  have hsq := Crystallography.div_sqrt_sumSq_sq (a := 0.4) (h := 2) (k := 0) (l := 0)
    (by norm_num)
  have hpos := Crystallography.div_sqrt_sumSq_pos (a := 0.4) (h := 2) (k := 0) (l := 0)
    (by norm_num) (by norm_num)
  have h2 : ((0.4 : ℝ) / 2) ^ 2
      = 0.4 ^ 2 / (((2 : ℤ) : ℝ) ^ 2 + ((0 : ℤ) : ℝ) ^ 2 + ((0 : ℤ) : ℝ) ^ 2) := by
    norm_num
  exact (pow_left_inj₀ hpos.le (by norm_num) two_ne_zero).mp (hsq.trans h2.symm)

/-- Positivity for `(111)`. -/
example : 0 < (0.4 : ℝ) / Real.sqrt (((1 : ℤ) : ℝ) ^ 2 + ((1 : ℤ) : ℝ) ^ 2 + ((1 : ℤ) : ℝ) ^ 2) :=
  Crystallography.div_sqrt_sumSq_pos (a := 0.4) (h := 1) (k := 1) (l := 1)
    (by norm_num) (by norm_num)
