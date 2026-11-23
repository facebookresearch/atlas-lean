/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.BoussinesqResultant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Boussinesq resultant checks

Concrete consumers of
`PhyslibExt.EarthScience.Geotechnical.BoussinesqResultant`: the unit
load at unit depth, the load-axis value, the sign change below the
surface convention, the totalized load point, and stress scaling.

## i. Overview

These are elaboration and boundary checks, not new results. The
negative-depth examples show why the resultant and axis-value results
carry the premise `0 < z`: both change sign at `z = -1`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Unit-load and axis values
- B. Sign, totalization, and scaling controls

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.BoussinesqResultant`
-/

open MeasureTheory Set Real

/-- Main nonzero witness: unit load at unit depth has resultant `1`. -/
example :
    (∫ r in Ioi 0, 2 * π * r
      * EarthScience.boussinesqVerticalStress 1 r 1) = 1 :=
  EarthScience.integral_boussinesq_resultant (by norm_num)

/-- Axis witness: unit load at unit depth has stress `3 / (2 π)`. -/
example : EarthScience.boussinesqVerticalStress 1 0 1 = 3 / (2 * π) := by
  rw [EarthScience.boussinesqVerticalStress_zero_radius (by norm_num)]
  norm_num

/-- The axis witness value is nonzero. -/
example : EarthScience.boussinesqVerticalStress 1 0 1 ≠ 0 := by
  rw [EarthScience.boussinesqVerticalStress_zero_radius (by norm_num)]
  positivity

/-- Negative-depth control: the resultant at `z = -1` is `-1`, not the
load `1`, so the positive-depth premise is necessary. -/
example :
    (∫ r in Ioi 0, 2 * π * r
      * EarthScience.boussinesqVerticalStress 1 r (-1)) = -1 := by
  have e : (fun r : ℝ => 2 * π * r
        * EarthScience.boussinesqVerticalStress 1 r (-1))
      = fun r => 2 * π * r
        * EarthScience.boussinesqVerticalStress (-1) r 1 := by
    funext r
    unfold EarthScience.boussinesqVerticalStress
    norm_num
  rw [e, EarthScience.integral_boussinesq_resultant (by norm_num)]

/-- Without a depth premise the resultant identity is false. -/
example :
    ¬ ∀ P z : ℝ, (∫ r in Ioi 0, 2 * π * r
      * EarthScience.boussinesqVerticalStress P r z) = P := by
  intro h
  have h10 := h 1 0
  rw [EarthScience.integral_boussinesq_resultant_zero_depth] at h10
  norm_num at h10

/-- Negative-depth axis control: the axis stress changes sign. -/
example :
    EarthScience.boussinesqVerticalStress 1 0 (-1) = -(3 / (2 * π)) := by
  unfold EarthScience.boussinesqVerticalStress; norm_num; ring

/-- Totalized load point: the closed form returns `0` at `r = z = 0`. -/
example (P : ℝ) : EarthScience.boussinesqVerticalStress P 0 0 = 0 := by
  simp [EarthScience.boussinesqVerticalStress]

/-- At `z = 0` the axis formula's right side is also totalized to `0`;
the axis result therefore keeps its positive-depth premise. -/
example (P : ℝ) :
    EarthScience.boussinesqVerticalStress P 0 0
      = 3 * P / (2 * π * (0 : ℝ) ^ 2) := by
  simp [EarthScience.boussinesqVerticalStress]

/-- Scaling: multiplying radius and depth by `l > 0` divides the stress
by `l ^ 2`. -/
example (r z l : ℝ) (hl : 0 < l) (hz : 0 < z) :
    l ^ 2 * EarthScience.boussinesqVerticalStress 1 (l * r) (l * z)
      = EarthScience.boussinesqVerticalStress 1 r z := by
  rw [EarthScience.boussinesqVerticalStress_eq_love,
    EarthScience.boussinesqVerticalStress_eq_love]
  have hscale : (l * r) ^ 2 + (l * z) ^ 2 = l ^ 2 * (r ^ 2 + z ^ 2) := by
    ring
  rw [hscale, Real.sqrt_mul (by positivity), Real.sqrt_sq hl.le]
  have h1 : 0 < √(r ^ 2 + z ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp
