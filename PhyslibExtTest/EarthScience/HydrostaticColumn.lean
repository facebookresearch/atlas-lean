/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.HydrostaticColumn

/-!
# Hydrostatic column checks

Concrete consumers of `PhyslibExt.EarthScience.HydrostaticColumn`:
a water column at the surface, at 10 m depth, and the signed
height-to-depth conversion.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`p0 = 101325`, `rho = 1000`, `g = 9.81`, the pressure at height `10`
is `3225` and at depth `10` is `199425`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Surface and 10 m values
- B. Height-to-depth conversion
-/

/-- Surface value: `p(0) = p0`. -/
example : (fun z : ℝ => (101325 : ℝ) - 1000 * 9.81 * z) 0 = 101325 := by
  have h := EarthScience.hydrostatic_pressure 101325 1000 9.81 0
  exact h.2

/-- Water column: `p(10) = 3225` at height `10`. -/
example : (fun z : ℝ => (101325 : ℝ) - 1000 * 9.81 * z) 10 = 3225 := by
  norm_num

/-- Depth value: `p(d) = p0 + rho * g * d` at depth `10` is `199425`. -/
example : (fun d : ℝ => (101325 : ℝ) + 1000 * 9.81 * d) 10 = 199425 := by
  norm_num

/-- The depth profile agrees with the height profile at `d = -z`. -/
example : (fun d : ℝ => (101325 : ℝ) + 1000 * 9.81 * d) 10 =
    (fun z : ℝ => (101325 : ℝ) - 1000 * 9.81 * z) (-10) := by
  have h := EarthScience.hydrostatic_pressure_depth 101325 1000 9.81 10
  exact h.2

/-- The public shape of the hydrostatic derivative. -/
example (p0 ρ g z : ℝ) :
    HasDerivAt (fun z => p0 - ρ * g * z) (-(ρ * g)) z :=
  (EarthScience.hydrostatic_pressure p0 ρ g z).1
