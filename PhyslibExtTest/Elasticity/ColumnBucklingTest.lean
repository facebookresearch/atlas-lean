/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Elasticity.ColumnBuckling

/-!
# Column buckling checks

Concrete consumers of `PhyslibExt.Elasticity.ColumnBuckling`: the
unit-shape clamped-clamped mode at `L = 2`, its equation at a point, and
the pinned sine that fails the clamped slope condition.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Clamped-clamped mode at `L = 2`
- B. A pinned sine is not clamped

## iv. References

- `PhyslibExt.Elasticity.ColumnBuckling`
-/

/-- Midspan value at `L = 2`: the mode value at `x = 1` is `2`. -/
example : Elasticity.clampedClampedMode 2 1 = 2 := by
  have h := Elasticity.clampedClampedMode_midspan (L := 2) (by norm_num)
  norm_num at h
  exact h

/-- The column equation at the midspan point for `EI = 3`, `L = 2`. -/
example :
    3 * iteratedDeriv 4 (Elasticity.clampedClampedMode 2) 1 +
        (4 * Real.pi ^ 2 * 3 / 2 ^ 2) *
          iteratedDeriv 2 (Elasticity.clampedClampedMode 2) 1 = 0 :=
  (Elasticity.clampedClamped_eigenpair (EI := 3) (L := 2) (by norm_num) (by norm_num)).1 1

/-- Boundary failure: the pinned-pinned sine `sin (πx / 2)` on `L = 2`
has slope `π / 2 ≠ 0` at `x = 0`, so it does not meet the clamped slope
condition. -/
example : deriv (fun x : ℝ => Real.sin (Real.pi * x / 2)) 0 ≠ 0 := by
  have h1 : HasDerivAt (fun x : ℝ => Real.pi * x / 2) (Real.pi / 2) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).const_mul (Real.pi / 2)
    rw [mul_one] at h
    have heq : (fun x : ℝ => Real.pi * x / 2)
        = fun x : ℝ => (Real.pi / 2) * x := by
      funext y
      ring
    rwa [heq]
  have hd := h1.sin.deriv
  have hval : Real.cos (Real.pi * (0 : ℝ) / 2) * (Real.pi / 2)
      = Real.pi / 2 := by simp
  rw [hd, hval]
  exact div_ne_zero (ne_of_gt Real.pi_pos) two_ne_zero
