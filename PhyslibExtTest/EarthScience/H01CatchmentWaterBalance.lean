/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.H01CatchmentWaterBalance

/-!
# Linear-reservoir catchment checks

Concrete consumers of `PhyslibExt.EarthScience.H01CatchmentWaterBalance`:
a numeric reservoir (`I = 3`, `k = 1 / 2`, `S0 = 10`), the equilibrium
case `S0 = I / k`, and the dry interval `I = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At `t = 2`
the numeric reservoir has storage `6 + 4 * exp (-1)`, derivative
`3 - (1 / 2) * S(2)`, and a closed integrated budget.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric reservoir
- B. Equilibrium and dry-interval boundaries

## iv. References

- `PhyslibExt.EarthScience.H01CatchmentWaterBalance`
-/

/-- Numeric reservoir at `t = 0`: storage is the initial storage. -/
example : (fun t => 3 / (1 / 2 : ℝ) + (10 - 3 / (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * t)) 0 = 10 :=
  EarthScience.storage_initial 3 (1 / 2) 10

/-- Numeric reservoir at `t = 2`: storage is `6 + 4 * exp (-1)`. -/
example : (fun t => 3 / (1 / 2 : ℝ) + (10 - 3 / (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * t)) 2
    = 6 + 4 * Real.exp (-1) := by
  norm_num

/-- Numeric reservoir: the profile satisfies the ODE at `t = 2`. -/
example : HasDerivAt
    (fun t => 3 / (1 / 2 : ℝ) + (10 - 3 / (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * t))
    (3 - (1 / 2 : ℝ) * (3 / (1 / 2 : ℝ) + (10 - 3 / (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * 2))) 2 :=
  EarthScience.hasDerivAt_storage_solution (by norm_num) 2

/-- Equilibrium boundary: `S0 = I / k` gives constant storage, so the
integrated budget closes with zero change at `t = 1`. -/
example : (∫ u in (0 : ℝ)..1, (3 / (1 / 2 : ℝ) + (6 - 3 / (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * u)))
      = 3 * 1 / (1 / 2 : ℝ) + (6 - 3 / (1 / 2 : ℝ)) * (1 - Real.exp (-(1 / 2 : ℝ) * 1)) / (1 / 2 : ℝ) ∧
    (3 / (1 / 2 : ℝ) + (6 - 3 / (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * 1)) - 6
      = 3 * 1 - (1 / 2 : ℝ) * (∫ u in (0 : ℝ)..1,
          (3 / (1 / 2 : ℝ) + (6 - 3 / (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * u))) :=
  EarthScience.integrated_water_budget (by norm_num) 1

/-- Dry interval boundary: `I = 0` gives pure decay, and the budget still closes. -/
example : (∫ u in (0 : ℝ)..1, (0 / (1 / 2 : ℝ) + (10 - 0 / (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * u)))
      = 0 * 1 / (1 / 2 : ℝ) + (10 - 0 / (1 / 2 : ℝ)) * (1 - Real.exp (-(1 / 2 : ℝ) * 1)) / (1 / 2 : ℝ) ∧
    (0 / (1 / 2 : ℝ) + (10 - 0 / (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * 1)) - 10
      = 0 * 1 - (1 / 2 : ℝ) * (∫ u in (0 : ℝ)..1,
          (0 / (1 / 2 : ℝ) + (10 - 0 / (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * u))) :=
  EarthScience.integrated_water_budget (by norm_num) 1
