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
# Linear-pressure resultant force and moment

## i. Overview

A linear pressure profile `p (z) = c * z` (pressure gradient `c`, depth
`z` from the zero-pressure datum) on a panel of width `w` over
`[a, b]` has resultant force `w * c * (b^2 - a^2) / 2` and first moment
about `z = 0` of `w * c * (b^3 - a^3) / 3`. This single producer serves
hydrostatic gates and Rankine walls; no pressure law is derived here.

## ii. Key results

- `PhyslibExt.Mechanics.LinearPressurePanel.linearPressureForce_eq`:
  resultant force.
- `PhyslibExt.Mechanics.LinearPressurePanel.linearPressureMoment_eq`:
  first moment about the datum.

## iii. Table of contents

- A. Resultant force and moment

## iv. References

- F. M. White, *Fluid Mechanics*, 7th edition, McGraw-Hill, 2011
  (hydrostatic force on plane surfaces).
-/

@[expose] public section

namespace PhyslibExt.Mechanics.LinearPressurePanel

/-! ## A. Resultant force and moment -/

/-- Resultant force from a linear pressure profile `p (z) = c * z` acting
over depth interval `[a, b]` on a panel of width `w`:
`∫ z in a..b, w * (c * z)`. Physically `w > 0`, `0 ≤ a < b`, `z` is depth
from the zero-pressure datum, and `c` is the pressure gradient; with `c` in
force/length³ and `w`, `z` in length, the force is in force units. The
identity also holds for all real inputs, as oriented interval integrals. -/
noncomputable def linearPressureForce (c w a b : ℝ) : ℝ :=
  ∫ z in a..b, w * (c * z)

/-- First moment, about depth zero, of the same linear pressure profile:
`∫ z in a..b, z * (w * (c * z))`. Same regime as `linearPressureForce`;
the moment is in force·length units about `z = 0`. -/
noncomputable def linearPressureMoment (c w a b : ℝ) : ℝ :=
  ∫ z in a..b, z * (w * (c * z))

/-- The resultant force of a linear pressure profile. -/
theorem linearPressureForce_eq (c w a b : ℝ) :
    linearPressureForce c w a b = w * c * (b ^ 2 - a ^ 2) / 2 := by
  unfold linearPressureForce
  simp only [← mul_assoc]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- The first moment of a linear pressure profile. -/
theorem linearPressureMoment_eq (c w a b : ℝ) :
    linearPressureMoment c w a b = w * c * (b ^ 3 - a ^ 3) / 3 := by
  unfold linearPressureMoment
  have h : ∀ z : ℝ, z * (w * (c * z)) = (w * c) * z ^ 2 := fun z => by ring
  simp only [h]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

end PhyslibExt.Mechanics.LinearPressurePanel
