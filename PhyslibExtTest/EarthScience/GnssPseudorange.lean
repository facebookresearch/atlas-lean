/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.GnssPseudorange
import Mathlib.Tactic.NormNum

/-!
# GNSS positioning and geodetic observations

Concrete consumers of `PhyslibExt.EarthScience.GnssPseudorange`.

## i. Overview

Numeric pseudorange directional derivative, with the value `7 / 5` checked, and the row-dot
identity.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.GnssPseudorange`
-/

open scoped InnerProductSpace

/-- Numeric case: `x₀ = (0,0,0)`, `s = (3,4,0)`, `d = (1,0,0)`, `db = 2`: derivative
`-3/5 + 2 = 7/5`. -/
example : HasDerivAt (fun t : ℝ =>
    ‖(0 : EuclideanSpace ℝ (Fin 3)) + t • !₂[1, 0, 0] - !₂[3, 4, 0]‖ + (0 + t * 2))
    (7 / 5 : ℝ) 0 := by
  have hs : ‖(0 : EuclideanSpace ℝ (Fin 3)) - !₂[3, 4, 0]‖ = 5 := by
    rw [zero_sub, norm_neg, EuclideanSpace.norm_eq,
      Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    simp [Fin.sum_univ_three]
    norm_num
  have hi : ⟪(0 : EuclideanSpace ℝ (Fin 3)) - !₂[3, 4, 0], !₂[1, 0, 0]⟫_ℝ = -3 := by
    simp [PiLp.inner_apply, Fin.sum_univ_three]
  refine (EarthScience.gnss_directional_derivative 0 !₂[3, 4, 0] !₂[1, 0, 0] 0 2
    ?_).congr_deriv ?_
  · intro h
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
    simp at h0
  · rw [hi, hs]
    norm_num

/-- Numeric row dot with the same geometry. -/
example :
    ⟪‖(0 : EuclideanSpace ℝ (Fin 3)) - !₂[3, 4, 0]‖⁻¹ •
        ((0 : EuclideanSpace ℝ (Fin 3)) - !₂[3, 4, 0]), !₂[1, 0, 0]⟫_ℝ + 1 * 2 =
      ⟪(0 : EuclideanSpace ℝ (Fin 3)) - !₂[3, 4, 0], !₂[1, 0, 0]⟫_ℝ /
        ‖(0 : EuclideanSpace ℝ (Fin 3)) - !₂[3, 4, 0]‖ + 2 :=
  EarthScience.gnss_jacobian_row_dot 0 !₂[3, 4, 0] !₂[1, 0, 0] 2
