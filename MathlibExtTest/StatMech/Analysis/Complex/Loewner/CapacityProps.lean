/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Loewner.CapacityProps

/-!
# Tests for `MathlibExt.Analysis.Complex.Loewner.CapacityProps`

* `hasHalfPlaneCapacity_halfDisk`, `halfDisk_capacity_eq` at `c = 3`.
* `hasHalfPlaneCapacity_neg_example`: `z - 1/z` has capacity `-1`.
* `HasHalfPlaneCapacity.scale` (factor `2`) and `.translate` applied to the half-disk map.
-/

@[expose] public section

open StatMech.SLE Complex

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.CapacityProps

example : HasHalfPlaneCapacity (fun z : ℂ => z + ((3 : ℝ) : ℂ) / z) 3 :=
  hasHalfPlaneCapacity_halfDisk 3

example {a : ℝ} (h : HasHalfPlaneCapacity (fun z : ℂ => z + ((3 : ℝ) : ℂ) / z) a) : a = 3 :=
  halfDisk_capacity_eq h

example : HasHalfPlaneCapacity (fun z : ℂ => z - z⁻¹) (-1) := hasHalfPlaneCapacity_neg_example

/-- Scaling by `2` multiplies the capacity by `4`. -/
example : HasHalfPlaneCapacity (fun z : ℂ => ((2 : ℝ) : ℂ) * ((z / ((2 : ℝ) : ℂ)) +
    ((1 : ℝ) : ℂ) / (z / ((2 : ℝ) : ℂ)))) (2 ^ 2 * 1) :=
  (hasHalfPlaneCapacity_halfDisk 1).scale (by norm_num)

example : HasHalfPlaneCapacity (fun z : ℂ => ((z - 1) + ((1 : ℝ) : ℂ) / (z - 1)) + 1) 1 :=
  (hasHalfPlaneCapacity_halfDisk 1).translate 1

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.CapacityProps
