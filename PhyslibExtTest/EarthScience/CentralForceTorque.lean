/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.CentralForceTorque

/-!
# Central-force-torque checks

Concrete consumers of `PhyslibExt.EarthScience.CentralForceTorque`: with
position `r = (1, 2, 3)`, a central force with `c = 5`, a radial force
with profile `φ (x) = x`, and an attractive force with `k = 2` all have
zero torque, while a non-central force such as `F = (0, 0, 1)` has
nonzero torque.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
boundary cases are `r = 0` (zero torque for any force) and `c = 0`
(zero force, zero torque). The non-central example shows the central
hypothesis is needed.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.CentralForceTorque`
-/

open EarthScience
open Matrix

/-- A central force with `c = 5` at `r = (1, 2, 3)` has zero torque. -/
example : torque ![1, 2, 3] ((5 : ℝ) • ![1, 2, 3]) = 0 :=
  central_force_torque_eq_zero ![1, 2, 3] 5

/-- A radial central force with any profile `φ` at any `r` has zero torque. -/
example (r : Fin 3 → ℝ) (φ : ℝ → ℝ) : torque r (φ ‖r‖ • r) = 0 :=
  radial_central_force_torque_eq_zero r φ

/-- An attractive central force with `k = 2` at `r = (1, 2, 3)` has zero torque. -/
example : torque ![1, 2, 3] ((-2 : ℝ) • ![1, 2, 3]) = 0 :=
  attractive_central_force_torque_eq_zero ![1, 2, 3] 2

/-- Boundary case: at `r = 0` a central force has zero torque. -/
example : torque (0 : Fin 3 → ℝ) ((5 : ℝ) • (0 : Fin 3 → ℝ)) = 0 :=
  central_force_torque_eq_zero 0 5

/-- Boundary case: zero force (`c = 0`) has zero torque. -/
example : torque ![1, 2, 3] ((0 : ℝ) • ![1, 2, 3]) = 0 :=
  central_force_torque_eq_zero ![1, 2, 3] 0

/-- Non-vacuous: a non-central force `F = (0, 0, 1)` at `r = (1, 2, 3)`
has nonzero torque, so the central hypothesis is needed. -/
example : torque ![1, 2, 3] ![0, 0, 1] ≠ 0 := by
  simp [torque, cross_apply]
