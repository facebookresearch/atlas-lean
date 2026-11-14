/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.CentralForceTorque

/-!
# Central-force-torque checks

Concrete consumers of `PhyslibExt.EarthScience.CentralForceTorque`: with
position `r = (1, 2, 3)`, a central force with `c = 5`, a radial force
with any profile of the Euclidean distance, and an attractive linear force
with `k = 2` all have zero torque, while a non-central force such as
`F = (0, 0, 1)` has nonzero torque.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
boundary cases are `r = 0` (zero torque for every force `F`) and `c = 0`
(zero force, zero torque). The non-central example shows the central
hypothesis is needed. The radial profile reads the Euclidean distance:
`(3, 4, 0)` and `(5, 0, 0)` have the same Euclidean length `5`, while
Mathlib's supremum norm on `Fin 3 → ℝ` gives them `4` and `5`.

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

/-- A radial central force with any profile `φ` of the Euclidean distance, at
any `r`, has zero torque. -/
example (r : Fin 3 → ℝ) (φ : ℝ → ℝ) : torque r (φ ‖WithLp.toLp 2 r‖ • r) = 0 :=
  radial_central_force_torque_eq_zero r φ

/-- The Euclidean distance of `(3, 4, 0)` is `5`. -/
example : ‖WithLp.toLp 2 (![3, 4, 0] : Fin 3 → ℝ)‖ = 5 := by
  rw [EuclideanSpace.norm_eq, show (5 : ℝ) = √(5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  congr 1
  simp [Fin.sum_univ_three]
  norm_num

/-- The Euclidean distance of `(5, 0, 0)` is also `5`, so a radial profile gives
`(3, 4, 0)` and `(5, 0, 0)` the same coefficient. -/
example : ‖WithLp.toLp 2 (![5, 0, 0] : Fin 3 → ℝ)‖ = 5 := by
  rw [EuclideanSpace.norm_eq, show (5 : ℝ) = √(5 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  congr 1
  simp [Fin.sum_univ_three]

/-- Mathlib's supremum norm is not the Euclidean distance: it gives `(3, 4, 0)`
norm `4`, not `5`. -/
example : ‖(![3, 4, 0] : Fin 3 → ℝ)‖ = 4 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
    fin_cases i <;> norm_num
  · simpa using norm_le_pi_norm (![3, 4, 0] : Fin 3 → ℝ) 1

/-- An attractive linear central force with `k = 2` at `r = (1, 2, 3)` has zero
torque. -/
example : torque ![1, 2, 3] ((-2 : ℝ) • ![1, 2, 3]) = 0 :=
  linear_central_force_torque_eq_zero ![1, 2, 3] 2

/-- A repulsive linear central force with `k = -2` at `r = (1, 2, 3)` has zero
torque. -/
example : torque ![1, 2, 3] ((-(-2) : ℝ) • ![1, 2, 3]) = 0 :=
  linear_central_force_torque_eq_zero ![1, 2, 3] (-2)

/-- Boundary case: at `r = 0` every force `F` has zero torque. -/
example (F : Fin 3 → ℝ) : torque 0 F = 0 := by
  simp [torque]

/-- Boundary case: zero force (`c = 0`) has zero torque. -/
example : torque ![1, 2, 3] ((0 : ℝ) • ![1, 2, 3]) = 0 :=
  central_force_torque_eq_zero ![1, 2, 3] 0

/-- Non-vacuous: a non-central force `F = (0, 0, 1)` at `r = (1, 2, 3)`
has nonzero torque, so the central hypothesis is needed. -/
example : torque ![1, 2, 3] ![0, 0, 1] ≠ 0 := by
  simp [torque, cross_apply]
