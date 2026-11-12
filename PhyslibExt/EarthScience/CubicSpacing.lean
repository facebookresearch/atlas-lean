/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum

/-!
# Crystal geometry: cubic interplanar spacing

For cubic lattice parameter `a > 0` and integer Miller vector
`(h, k, l) ≠ 0`, interplanar spacing `d = a / √(h ^ 2 + k ^ 2 + l ^ 2)`.

## i. Overview

`a` and `d` are lengths. The spacing is defined by the Euclidean
plane-normal definition with the direct/reciprocal convention frozen:
the reciprocal-lattice vector has length `√(h ^ 2 + k ^ 2 + l ^ 2) / a`,
and `d` is its reciprocal. No general space-group classification or
noncubic metric is assumed; the `(0, 0, 0)` index vector is excluded.

## ii. Key results

- `EarthScience.cubic_spacing_sq`: `d ^ 2 = a ^ 2 / (h ^ 2 + k ^ 2 + l ^ 2)`.
- `EarthScience.cubic_spacing_pos`: the spacing is positive.
- `EarthScience.cubic_spacing_100`, `cubic_spacing_110`,
  `cubic_spacing_111`: the `(100)`, `(110)`, `(111)` planes.

## iii. Table of contents

- A. Cubic interplanar spacing

## iv. References

- `Real.sq_sqrt`, `Real.sqrt_pos_of_pos` in Mathlib.

## A. Cubic interplanar spacing
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Cubic interplanar spacing: `d ^ 2 = a ^ 2 / (h ^ 2 + k ^ 2 + l ^ 2)`. -/
theorem cubic_spacing_sq {a : ℝ} (ha : 0 < a) {h k l : ℤ}
    (hpos : 0 < (h : ℝ) ^ 2 + (k : ℝ) ^ 2 + (l : ℝ) ^ 2) :
    (a / Real.sqrt ((h : ℝ) ^ 2 + (k : ℝ) ^ 2 + (l : ℝ) ^ 2)) ^ 2
      = a ^ 2 / ((h : ℝ) ^ 2 + (k : ℝ) ^ 2 + (l : ℝ) ^ 2) := by
  rw [div_pow, Real.sq_sqrt (le_of_lt hpos)]

/-- Cubic interplanar spacing is positive. -/
theorem cubic_spacing_pos {a : ℝ} (ha : 0 < a) {h k l : ℤ}
    (hpos : 0 < (h : ℝ) ^ 2 + (k : ℝ) ^ 2 + (l : ℝ) ^ 2) :
    0 < a / Real.sqrt ((h : ℝ) ^ 2 + (k : ℝ) ^ 2 + (l : ℝ) ^ 2) := by
  exact div_pos ha (Real.sqrt_pos_of_pos hpos)

set_option linter.unusedVariables false in
/-- Cubic spacing for `(100)`: `d = a`. -/
theorem cubic_spacing_100 {a : ℝ} (ha : 0 < a) :
    a / Real.sqrt ((1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = a := by
  have h : ((1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 1 := by norm_num
  rw [h, Real.sqrt_one, div_one]

set_option linter.unusedVariables false in
/-- Cubic spacing for `(110)`: `d = a / √2`. -/
theorem cubic_spacing_110 {a : ℝ} (ha : 0 < a) :
    a / Real.sqrt ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = a / Real.sqrt 2 := by
  have h : ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 2 := by norm_num
  rw [h]

set_option linter.unusedVariables false in
/-- Cubic spacing for `(111)`: `d = a / √3`. -/
theorem cubic_spacing_111 {a : ℝ} (ha : 0 < a) :
    a / Real.sqrt ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2) = a / Real.sqrt 3 := by
  have h : ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2) = 3 := by norm_num
  rw [h]

end EarthScience
