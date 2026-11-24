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

Focused checks for
`PhyslibExt.FluidDynamics.Traffic.VehicleAccounting`: one cell
with inflow `5` and outflow `2` gains `3` vehicles at `dt = 1`;
a two-cell periodic chain (`F 0 = F 2`, internal face `F 1 = 2`)
gains nothing, with the internal flux cancelling through the
summed update; and the discrete-balance bridge at the same
witness.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic.VehicleAccounting

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

/-- Two-cell periodic chain: the summed update is zero, through
`total_vehicle_change` (the internal face cancels). -/
example : ∑ i ∈ Finset.range 2,
      (2 : ℝ) * (((fun _ => (10 : ℝ)) i
        + 1 / 2 * ((fun j => if j = 1 then (2 : ℝ) else 5) i
          - (fun j => if j = 1 then (2 : ℝ) else 5) (i + 1)))
        - (fun _ => (10 : ℝ)) i)
    = 0 := by
  have h := total_vehicle_change (n := 2) (fun _ => (10 : ℝ))
    (fun j => if j = 1 then (2 : ℝ) else 5) 1 2 (by norm_num)
  simpa using h

/-- The discrete-balance bridge at the one-cell witness. -/
example : ∑ i ∈ Finset.range 1,
      (2 : ℝ) * (((fun _ => (10 : ℝ)) i
        + 1 / 2 * ((fun j => if j = 0 then (5 : ℝ) else 2) i
          - (fun j => if j = 0 then (5 : ℝ) else 2) (i + 1)))
        - (fun _ => (10 : ℝ)) i)
    = 2 * 1
      * MathlibExt.Analysis.ODE.ContinuumBalances.totalDiscreteChange
          ⟨(2 : ℝ), by norm_num⟩
          (fun j : Fin (1 + 1) =>
            (fun j => if j = 0 then (5 : ℝ) else 2) j.val) :=
  total_vehicle_change_eq_discrete (fun _ => (10 : ℝ))
    (fun j => if j = 0 then (5 : ℝ) else 2) 1 2 (by norm_num)
