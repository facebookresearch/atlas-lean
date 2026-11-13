/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination

/-!
# General circulation: conservation of absolute axial angular momentum

An air parcel that starts at rest at the equator keeps its absolute axial
angular momentum per unit mass, `Ω a²`, as it moves poleward in a
torque-free, inviscid, axisymmetric ideal model. At latitude `φ` its
absolute angular momentum is `(Ω a cos φ + u) (a cos φ)`, where `u` is the
eastward wind, so conservation forces
`u = Ω a sin²φ / cos φ`.

## i. Overview

Fix Earth's rotation rate `Ω` and radius `a > 0`. The parcel's angular
momentum at the equator, where `u = 0` and `cos 0 = 1`, is `Ω a²`. The
theorem below solves the conservation equation
`(Ω a cos φ + u) (a cos φ) = Ω a²` for `u`, using `sin²φ + cos²φ = 1`
and `cos φ ≠ 0` for `|φ| < π/2`. At the equator the formula gives `u = 0`,
as it must. This is not the Held–Hou cell width and not an actual
circulation prediction; there is no polar continuation.

## ii. Key results

- `EarthScience.angular_momentum_zonal_wind`: conservation gives
  `u = Ω a sin²φ / cos φ`.
- `EarthScience.angular_momentum_zonal_wind_equator`: at `φ = 0`, `u = 0`.

## iii. Table of contents

- A. Zonal wind from angular-momentum conservation

## iv. References

- `Real.sin_sq_add_cos_sq` in
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean` (Mathlib).

## A. Zonal wind from angular-momentum conservation
-/

@[expose] public section

namespace EarthScience

/-- Conservation of absolute axial angular momentum: an air parcel starting
at rest at the equator has absolute angular momentum per unit mass `Ω a²`.
If at latitude `φ` its eastward wind is `u`, conservation
`(Ω a cos φ + u) (a cos φ) = Ω a²` forces
`u = Ω a sin²φ / cos φ`. -/
theorem angular_momentum_zonal_wind (Ω a φ u : ℝ) (ha : 0 < a)
    (hφ : |φ| < Real.pi / 2)
    (hcons : (Ω * a * Real.cos φ + u) * (a * Real.cos φ) = Ω * a ^ 2) :
    u = Ω * a * (Real.sin φ) ^ 2 / Real.cos φ := by
  have hcos : 0 < Real.cos φ := by
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo]
    exact abs_lt.mp hφ
  have hC : Real.cos φ ≠ 0 := ne_of_gt hcos
  have hA : a ≠ 0 := ne_of_gt ha
  have hpyth : (Real.sin φ) ^ 2 + (Real.cos φ) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq φ
  have e1 : u * (a * Real.cos φ)
      = Ω * a ^ 2 - Ω * a * Real.cos φ * (a * Real.cos φ) := by
    linear_combination hcons
  have e1' : u * Real.cos φ * a = Ω * a * (Real.sin φ) ^ 2 * a := by
    linear_combination e1 - (Ω * a ^ 2) * hpyth
  have e2 : u * Real.cos φ = Ω * a * (Real.sin φ) ^ 2 :=
    mul_right_cancel₀ hA e1'
  rw [eq_div_iff hC]
  linear_combination e2

/-- At the equator the conserved parcel is still at rest: the formula gives
`u = 0` at `φ = 0`. -/
theorem angular_momentum_zonal_wind_equator (Ω a u : ℝ) (ha : 0 < a)
    (hcons : (Ω * a * Real.cos 0 + u) * (a * Real.cos 0) = Ω * a ^ 2) :
    u = 0 := by
  rw [Real.cos_zero] at hcons
  have hA : a ≠ 0 := ne_of_gt ha
  have e1 : u * a = 0 := by linear_combination hcons
  exact (mul_eq_zero.mp e1).resolve_right hA

end EarthScience
