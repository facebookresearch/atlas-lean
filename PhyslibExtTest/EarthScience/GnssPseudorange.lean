/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.GnssPseudorange

/-!
# GNSS positioning and geodetic observations

Concrete consumers of `PhyslibExt.EarthScience.GnssPseudorange`.

## i. Overview

Numeric pseudorange directional derivative and a rank-identification instance.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.GnssPseudorange`
-/

/-- Numeric case: `x₀ = (0,0,0)`, `s = (3,4,0)`, `d = (1,0,0)`, `db = 2`: derivative `-3/5 + 2 = 7/5`. -/
example : HasDerivAt (fun t => Real.sqrt (((0 : ℝ) + t * 1 - 3) ^ 2 +
    ((0 : ℝ) + t * 0 - 4) ^ 2 + ((0 : ℝ) + t * 0 - 0) ^ 2) + (0 + t * 2))
    (((0 - 3 : ℝ) * 1 + (0 - 4) * 0 + (0 - 0) * 0) /
      Real.sqrt ((0 - 3 : ℝ) ^ 2 + (0 - 4) ^ 2 + (0 - 0) ^ 2) + 2) 0 :=
  EarthScience.gnss_directional_derivative (0, 0, 0) (3, 4, 0) (1, 0, 0) 0 2 (by simp)

/-- Numeric row dot with the same geometry. -/
example : (0 - 3 : ℝ) / Real.sqrt ((0 - 3 : ℝ) ^ 2 + (0 - 4) ^ 2 + (0 - 0) ^ 2) * 1 +
    (0 - 4) / Real.sqrt ((0 - 3 : ℝ) ^ 2 + (0 - 4) ^ 2 + (0 - 0) ^ 2) * 0 +
    (0 - 0) / Real.sqrt ((0 - 3 : ℝ) ^ 2 + (0 - 4) ^ 2 + (0 - 0) ^ 2) * 0 + 1 * 2 =
    ((0 - 3 : ℝ) * 1 + (0 - 4) * 0 + (0 - 0) * 0) /
      Real.sqrt ((0 - 3 : ℝ) ^ 2 + (0 - 4) ^ 2 + (0 - 0) ^ 2) + 2 :=
  EarthScience.gnss_jacobian_row_dot (0, 0, 0) (3, 4, 0) (1, 0, 0) 2 (by norm_num)

/-- Identity matrix has injective `mulVec`, so a zero product forces `δ = 0`. -/
example (δ : Fin 4 → ℝ) (h : (1 : Matrix (Fin 4) (Fin 4) ℝ).mulVec δ = 0) : δ = 0 :=
  EarthScience.gnss_full_rank_identifies 1 δ (by simp [Function.Injective]) h
