/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum

/-!
# Cubic interplanar spacing formula: algebraic identities

For real `a` and integers `h, k, l` with `h ^ 2 + k ^ 2 + l ^ 2 > 0`, this
file proves algebraic facts about the real expression
`a / √(h ^ 2 + k ^ 2 + l ^ 2)`; only its positivity needs `a > 0`.

## i. Overview

Textbooks identify `a / √(h ^ 2 + k ^ 2 + l ^ 2)` with the interplanar spacing
`d_hkl` of the `(hkl)` planes of a simple cubic lattice with lattice parameter
`a` (see References). Lattices, lattice planes, and reciprocal vectors are not
formalized here, so that identification is not kernel-checked: the theorems
below are algebraic identities about the expression, not crystallographic
results.

Reciprocal convention of the cited formula: with the physics normalization
`a_i · b_j = 2π δ_ij`, the simple-cubic reciprocal lattice is spanned by
`(2π / a) e_i`, so `G_hkl = (2π / a) (h, k, l)` has length
`(2π / a) √(h ^ 2 + k ^ 2 + l ^ 2)` and the spacing is `d = 2π / |G_hkl|`. In
the crystallographic normalization without `2π`,
`|G_hkl| = √(h ^ 2 + k ^ 2 + l ^ 2) / a` and `d = 1 / |G_hkl|`. Both give
`d = a / √(h ^ 2 + k ^ 2 + l ^ 2)`.

## ii. Key results

- `EarthScience.div_sqrt_sumSq_sq`:
  `(a / √(h ^ 2 + k ^ 2 + l ^ 2)) ^ 2 = a ^ 2 / (h ^ 2 + k ^ 2 + l ^ 2)`.
- `EarthScience.div_sqrt_sumSq_pos`: the expression is positive when `a > 0`.
- `EarthScience.div_sqrt_sumSq_100`, `div_sqrt_sumSq_110`,
  `div_sqrt_sumSq_111`: the index patterns `(1, 0, 0)`, `(1, 1, 0)`,
  `(1, 1, 1)` give `a`, `a / √2`, `a / √3`.

## iii. Table of contents

- A. Algebraic identities for `a / √(h ^ 2 + k ^ 2 + l ^ 2)`

## iv. References

- C. Kittel, *Introduction to Solid State Physics*, 8th ed., Wiley, 2005,
  Chapter 2 (the reciprocal lattice; end-of-chapter problem on interplanar
  separation: `d(hkl) = 2π / |G|` and, for a simple cubic lattice,
  `d ^ 2 = a ^ 2 / (h ^ 2 + k ^ 2 + l ^ 2)`).
- N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Holt, Rinehart and
  Winston, 1976, Chapter 5 (the reciprocal lattice, with
  `a_i · b_j = 2π δ_ij`; section "Lattice planes": adjacent planes of a
  family are `2π / K` apart, `K` the shortest reciprocal lattice vector
  normal to them).
- `Real.sq_sqrt`, `Real.sqrt_pos_of_pos` in Mathlib.

## A. Algebraic identities for `a / √(h ^ 2 + k ^ 2 + l ^ 2)`
-/

@[expose] public section

namespace EarthScience

/-- Algebraic identity:
`(a / √(h ^ 2 + k ^ 2 + l ^ 2)) ^ 2 = a ^ 2 / (h ^ 2 + k ^ 2 + l ^ 2)` when
`h ^ 2 + k ^ 2 + l ^ 2 > 0`. It squares the textbook cubic-spacing expression;
it does not derive a spacing from lattice planes. -/
theorem div_sqrt_sumSq_sq {a : ℝ} {h k l : ℤ}
    (hpos : 0 < (h : ℝ) ^ 2 + (k : ℝ) ^ 2 + (l : ℝ) ^ 2) :
    (a / Real.sqrt ((h : ℝ) ^ 2 + (k : ℝ) ^ 2 + (l : ℝ) ^ 2)) ^ 2
      = a ^ 2 / ((h : ℝ) ^ 2 + (k : ℝ) ^ 2 + (l : ℝ) ^ 2) := by
  rw [div_pow, Real.sq_sqrt (le_of_lt hpos)]

/-- The expression `a / √(h ^ 2 + k ^ 2 + l ^ 2)` is positive when `a > 0` and
`h ^ 2 + k ^ 2 + l ^ 2 > 0`. -/
theorem div_sqrt_sumSq_pos {a : ℝ} (ha : 0 < a) {h k l : ℤ}
    (hpos : 0 < (h : ℝ) ^ 2 + (k : ℝ) ^ 2 + (l : ℝ) ^ 2) :
    0 < a / Real.sqrt ((h : ℝ) ^ 2 + (k : ℝ) ^ 2 + (l : ℝ) ^ 2) := by
  exact div_pos ha (Real.sqrt_pos_of_pos hpos)

/-- Index pattern `(1, 0, 0)`: `a / √(1 ^ 2 + 0 ^ 2 + 0 ^ 2) = a`. -/
theorem div_sqrt_sumSq_100 {a : ℝ} :
    a / Real.sqrt ((1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = a := by
  have h : ((1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 1 := by norm_num
  rw [h, Real.sqrt_one, div_one]

/-- Index pattern `(1, 1, 0)`: `a / √(1 ^ 2 + 1 ^ 2 + 0 ^ 2) = a / √2`. -/
theorem div_sqrt_sumSq_110 {a : ℝ} :
    a / Real.sqrt ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = a / Real.sqrt 2 := by
  have h : ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 2 := by norm_num
  rw [h]

/-- Index pattern `(1, 1, 1)`: `a / √(1 ^ 2 + 1 ^ 2 + 1 ^ 2) = a / √3`. -/
theorem div_sqrt_sumSq_111 {a : ℝ} :
    a / Real.sqrt ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2) = a / Real.sqrt 3 := by
  have h : ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2) = 3 := by norm_num
  rw [h]

end EarthScience
