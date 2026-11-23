/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Winkler footing resultant force and moment

## i. Overview

A rigid footing on a Winkler foundation with affine contact pressure
`p (x) = ks * (a + b * x)` on `[-B / 2, B / 2]` (subgrade modulus `ks`,
uniform settlement `a`, small rotation `b`, width `B`) has resultant
force `ks * B * a` and center moment `ks * B ^ 3 * b / 12`, per unit
out-of-plane length. The antisymmetric pressure part carries the moment
and cancels in the force.

## ii. Key results

- `EarthScience.footingResultantForce_eq`: resultant force.
- `EarthScience.footingResultantMoment_eq`: center moment.

## iii. Table of contents

- A. Resultant force and moment

## iv. References

- J. E. Bowles, *Foundation Analysis and Design*, 5th edition,
  McGraw-Hill, 1996 (Winkler subgrade reaction).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Resultant force and moment -/

/-- Resultant force per unit out-of-plane length from the affine contact
pressure `p (x) = ks * (a + b * x)` on `[-B / 2, B / 2]`. Here `ks` is the
subgrade modulus (pressure/length, F/L³), `a` is uniform settlement (L),
`b` is small rotation (rad), `x` is the lateral coordinate from the
footing center (L), and `B` is footing width (L). The force is F/L.
Physical regime: `B > 0`, `ks > 0`, rigid footing in full Winkler
contact, integrated without a no-tension cutoff. The identity holds for
all real inputs as an oriented interval integral. -/
noncomputable def footingResultantForce (ks a b B : ℝ) : ℝ :=
  ∫ x in (-B / 2)..(B / 2), ks * (a + b * x)

/-- Moment about the center, per unit out-of-plane length, of the same
affine contact pressure; positive when pressure rises toward `+x`, in
F·L/L = F. Same regime and conventions as `footingResultantForce`. -/
noncomputable def footingResultantMoment (ks a b B : ℝ) : ℝ :=
  ∫ x in (-B / 2)..(B / 2), x * (ks * (a + b * x))

/-- The resultant force is `ks * B * a`: the antisymmetric part cancels. -/
theorem footingResultantForce_eq (ks a b B : ℝ) :
    footingResultantForce ks a b B = ks * B * a := by
  unfold footingResultantForce
  have h1 : IntervalIntegrable (fun _ : ℝ => ks * a)
      MeasureTheory.volume (-B / 2) (B / 2) := intervalIntegrable_const
  have hc2 : Continuous fun x : ℝ => (ks * b) * x := by fun_prop
  have h2 : IntervalIntegrable (fun x : ℝ => (ks * b) * x)
      MeasureTheory.volume (-B / 2) (B / 2) := hc2.intervalIntegrable _ _
  have hfun : (fun x : ℝ => ks * (a + b * x)) = fun x => (ks * a) + (ks * b) * x := by
    ext x; ring
  rw [hfun, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
    smul_eq_mul]
  ring

/-- The resultant moment is `ks * B ^ 3 * b / 12`. -/
theorem footingResultantMoment_eq (ks a b B : ℝ) :
    footingResultantMoment ks a b B = ks * B ^ 3 * b / 12 := by
  unfold footingResultantMoment
  have hc1 : Continuous fun x : ℝ => (ks * a) * x := by fun_prop
  have h1 : IntervalIntegrable (fun x : ℝ => (ks * a) * x)
      MeasureTheory.volume (-B / 2) (B / 2) := hc1.intervalIntegrable _ _
  have hc2 : Continuous fun x : ℝ => (ks * b) * x ^ 2 := by fun_prop
  have h2 : IntervalIntegrable (fun x : ℝ => (ks * b) * x ^ 2)
      MeasureTheory.volume (-B / 2) (B / 2) := hc2.intervalIntegrable _ _
  have hfun : (fun x : ℝ => x * (ks * (a + b * x))) =
      fun x => (ks * a) * x + (ks * b) * x ^ 2 := by
    ext x; ring
  rw [hfun, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_id, integral_pow]
  ring

end EarthScience
