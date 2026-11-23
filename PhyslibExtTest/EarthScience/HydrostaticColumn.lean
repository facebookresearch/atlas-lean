/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.HydrostaticColumn

/-!
# Hydrostatic column checks

Concrete consumers of `PhyslibExt.EarthScience.HydrostaticColumn`:
a water column at the surface and 10 m below it, its pressure gradient,
the signed height-to-depth conversion, and the physical regime.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`p0 = 101325`, `rho = 1000`, `g = 9.81`, the pressure 10 m below the
surface (height `-10`, depth `10`) is `199425`, and the pressure
changes by `-9810` per metre of height (`+9810` per metre of depth).
In the physical regime the pressure 10 m down exceeds the pressure 5 m
down, and below the surface it never drops under `p0`; 20 m above the
surface the signed profile is negative, outside that regime.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Surface and 10 m values
- B. Pressure gradients and height-to-depth conversion
- C. Physical regime
-/

/-- Surface value: `p(0) = p0`. -/
example : (fun z : ℝ => (101325 : ℝ) - 1000 * 9.81 * z) 0 = 101325 := by
  have h := EarthScience.hydrostatic_pressure 101325 1000 9.81 0
  exact h.2

/-- Water column: `p = 199425` at height `-10`, 10 m below the surface. -/
example : (fun z : ℝ => (101325 : ℝ) - 1000 * 9.81 * z) (-10) = 199425 := by
  norm_num

/-- Depth value: `p(d) = p0 + rho * g * d` at depth `10` is `199425`. -/
example : (fun d : ℝ => (101325 : ℝ) + 1000 * 9.81 * d) 10 = 199425 := by
  norm_num

/-- Pressure gradient in height coordinates: `dp/dz = -9810` Pa/m at every height. -/
example (z : ℝ) : HasDerivAt (fun z : ℝ => (101325 : ℝ) - 1000 * 9.81 * z) (-9810) z := by
  convert (EarthScience.hydrostatic_pressure 101325 1000 9.81 z).1 using 1
  norm_num

/-- Pressure gradient in depth coordinates: `dp/dd = 9810` Pa/m at every depth. -/
example (d : ℝ) : HasDerivAt (fun d : ℝ => (101325 : ℝ) + 1000 * 9.81 * d) 9810 d := by
  convert (EarthScience.hydrostatic_pressure_depth 101325 1000 9.81 d).1 using 1
  norm_num

/-- The depth profile agrees with the height profile at `d = -z`. -/
example : (fun d : ℝ => (101325 : ℝ) + 1000 * 9.81 * d) 10 =
    (fun z : ℝ => (101325 : ℝ) - 1000 * 9.81 * z) (-10) := by
  have h := EarthScience.hydrostatic_pressure_depth 101325 1000 9.81 10
  exact h.2

/-- Physical regime: the water-column pressure 10 m below the surface exceeds the
pressure 5 m below it. -/
example : (fun d : ℝ => (101325 : ℝ) + 1000 * 9.81 * d) 5 <
    (fun d : ℝ => (101325 : ℝ) + 1000 * 9.81 * d) 10 :=
  (EarthScience.hydrostatic_pressure_physical (by norm_num) (by norm_num) (by norm_num)).1
    (by norm_num)

/-- Physical regime: at every depth below the surface the water-column pressure is at
least the surface pressure `101325`, hence positive. -/
example (d : ℝ) (hd : 0 ≤ d) :
    101325 ≤ (101325 : ℝ) + 1000 * 9.81 * d ∧ 0 < (101325 : ℝ) + 1000 * 9.81 * d :=
  (EarthScience.hydrostatic_pressure_physical (by norm_num) (by norm_num) (by norm_num)).2 d hd

/-- Outside the physical regime: 20 m above the surface the signed height profile is
negative. -/
example : (fun z : ℝ => (101325 : ℝ) - 1000 * 9.81 * z) 20 < 0 := by
  norm_num
