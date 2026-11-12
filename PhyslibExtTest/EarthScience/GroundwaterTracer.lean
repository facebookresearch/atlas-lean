/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.GroundwaterTracer

/-!
# Groundwater-tracer capstone checks

Concrete consumers of `PhyslibExt.EarthScience.GroundwaterTracer`:
Darcy flux and pore velocity at the stated inputs, and the tracer
update at `ν = 1 / 4, c₁ = 2, c₂ = 1` (updated `7 / 4, 5 / 4`, sum `3`),
plus the `ν = 0` boundary (no movement).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Darcy flux and pore velocity
- B. Tracer update

## iv. References

- `PhyslibExt.EarthScience.GroundwaterTracer`
-/

/-- Darcy flux at the stated inputs. -/
example : -(1 / 10000 : ℝ) * (1 / 100) = -1 / 1000000 :=
  EarthScience.darcy_flux_value

/-- Pore velocity at the stated inputs. -/
example : (-1 / 1000000 : ℝ) / (1 / 4) = -4 / 1000000 :=
  EarthScience.pore_velocity_value

/-- Tracer update at `ν = 1 / 4, c₁ = 2, c₂ = 1`: updated values `7 / 4, 5 / 4`. -/
example : ((1 - 1 / 4 : ℝ) * 2 + (1 / 4) * 1) = 7 / 4 ∧
    ((1 - 1 / 4 : ℝ) * 1 + (1 / 4) * 2) = 5 / 4 := by
  norm_num

/-- Tracer mass conserved at `ν = 1 / 4, c₁ = 2, c₂ = 1`: sum stays `3`. -/
example : ((1 - 1 / 4 : ℝ) * 2 + (1 / 4) * 1)
    + ((1 - 1 / 4 : ℝ) * 1 + (1 / 4) * 2) = 2 + 1 :=
  EarthScience.tracer_update_mass_conserved (ν := 1 / 4) (c₁ := 2) (c₂ := 1)

/-- Tracer nonnegativity at `ν = 1 / 4, c₁ = 2, c₂ = 1`. -/
example : 0 ≤ (1 - 1 / 4 : ℝ) * 2 + (1 / 4) * 1 ∧
    0 ≤ (1 - 1 / 4 : ℝ) * 1 + (1 / 4) * 2 :=
  EarthScience.tracer_update_nonneg (ν := 1 / 4) (c₁ := 2) (c₂ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `ν = 0` boundary: no movement, `c₁' = c₁, c₂' = c₂`. -/
example : ((1 - 0 : ℝ) * 2 + 0 * 1) = 2 ∧ ((1 - 0 : ℝ) * 1 + 0 * 2) = 1 := by
  norm_num
