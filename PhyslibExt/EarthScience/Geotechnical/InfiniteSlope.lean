/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Infinite-slope slab geometry

## i. Overview

For a plane-parallel slab on a slope of angle `beta`, with slip-plane
area `A` and vertical depth `z`, the slab volume is `A * z * cos beta`
(the normal thickness is `z * cos beta`). Resolving the slab weight per
unit slip-plane area gives the normal stress `gamma * z * cos beta ^ 2`
and the driving shear stress `gamma * z * sin beta * cos beta`, where
`gamma` is unit weight and `z` is vertical depth, not normal thickness.
The model assumes the translation-invariant side-face resultants of the
infinite slope cancel, so the basal traction balances the resolved
weight. No strength law or stability criterion is stated here.

## ii. Key results

- `EarthScience.infiniteSlopeSlabVolume`: slab volume.
- `EarthScience.infiniteSlopeNormalStress_eq`,
  `EarthScience.infiniteSlopeDrivingStress_eq`: weight components per
  unit area are the two stresses.
- `EarthScience.infiniteSlopeDriving_eq_normal_mul_tan`: driving stress
  is normal stress times `tan beta` on a genuine slope.

## iii. Table of contents

- A. Slab volume and resolved stresses

## iv. References

- B. M. Das and K. Sobhan, *Principles of Geotechnical Engineering*,
  10th edition, Cengage, 2022 (infinite slope without seepage).
- R. F. Craig, *Craig's Soil Mechanics*, 8th edition, CRC Press, 2012
  (infinite slopes).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Slab volume and resolved stresses -/

/-- Volume of a plane-parallel infinite-slope slab per slip-plane area `A`,
for vertical depth `z` and slope angle `beta` in radians:
`A * z * cos beta`. The thickness normal to the slip plane is
`z * cos beta`. -/
noncomputable def infiniteSlopeSlabVolume (A z beta : ℝ) : ℝ :=
  A * z * Real.cos beta

/-- Normal stress on the slip plane from the slab weight:
`gamma * z * cos beta ^ 2`, where `gamma` is unit weight and
`z` is vertical depth (not normal thickness). -/
noncomputable def infiniteSlopeNormalStress (gamma z beta : ℝ) : ℝ :=
  gamma * z * Real.cos beta ^ 2

/-- Driving shear stress on the slip plane from the slab weight:
`gamma * z * sin beta * cos beta`, with `z` vertical depth. -/
noncomputable def infiniteSlopeDrivingStress (gamma z beta : ℝ) : ℝ :=
  gamma * z * Real.sin beta * Real.cos beta

/-- The normal component of slab weight per slip-plane area is the
normal stress. -/
theorem infiniteSlopeNormalStress_eq {A gamma z beta : ℝ} (hA : 0 < A) :
    gamma * infiniteSlopeSlabVolume A z beta * Real.cos beta / A
      = infiniteSlopeNormalStress gamma z beta := by
  have hA0 : A ≠ 0 := hA.ne'
  unfold infiniteSlopeSlabVolume infiniteSlopeNormalStress
  field_simp

/-- The downslope component of slab weight per slip-plane area is the
driving shear stress. -/
theorem infiniteSlopeDrivingStress_eq {A gamma z beta : ℝ} (hA : 0 < A) :
    gamma * infiniteSlopeSlabVolume A z beta * Real.sin beta / A
      = infiniteSlopeDrivingStress gamma z beta := by
  have hA0 : A ≠ 0 := hA.ne'
  unfold infiniteSlopeSlabVolume infiniteSlopeDrivingStress
  field_simp

/-- On a genuine slope, driving stress is normal stress times `tan beta`. -/
theorem infiniteSlopeDriving_eq_normal_mul_tan {gamma z beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta : beta < Real.pi / 2) :
    infiniteSlopeDrivingStress gamma z beta
      = infiniteSlopeNormalStress gamma z beta * Real.tan beta := by
  have hcos : Real.cos beta ≠ 0 := by
    have hmem : beta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · have hpi : 0 < Real.pi := Real.pi_pos
        linarith
      · exact hbeta
    exact (Real.cos_pos_of_mem_Ioo hmem).ne'
  unfold infiniteSlopeDrivingStress infiniteSlopeNormalStress
  rw [Real.tan_eq_sin_div_cos]
  field_simp

end EarthScience
