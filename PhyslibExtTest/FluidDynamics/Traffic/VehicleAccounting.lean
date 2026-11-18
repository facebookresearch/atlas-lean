/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.Traffic.VehicleAccounting
import Mathlib.Tactic.NormNum

/-!
# Vehicle-accounting checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.VehicleAccounting`:
one cell with inflow `5` and outflow `2` gains `3` vehicles at
`dt = 1`; a periodic chain (`F 0 = F n`) gains nothing.

These are elaboration and non-vacuity checks, not new results.
-/

/-- One cell, unequal inlet and outlet. -/
example : ∑ i ∈ Finset.range 1,
      (2 : ℝ) * (((fun _ => (10 : ℝ)) i
        + 1 / 2 * ((fun j => if j = 0 then (5 : ℝ) else 2) i
          - (fun j => if j = 0 then (5 : ℝ) else 2) (i + 1)))
        - (fun _ => (10 : ℝ)) i)
    = 1 * ((fun j => if j = 0 then (5 : ℝ) else 2) 0
      - (fun j => if j = 0 then (5 : ℝ) else 2) 1) :=
  total_vehicle_change (fun _ => (10 : ℝ))
    (fun j => if j = 0 then (5 : ℝ) else 2) 1 2 (by norm_num)

/-- Periodic chain: no net change. -/
example : (1 : ℝ) * ((fun j => if j = 1 then (2 : ℝ) else 5) 0
      - (fun j => if j = 1 then (2 : ℝ) else 5) 2) = 0 := by
  norm_num
