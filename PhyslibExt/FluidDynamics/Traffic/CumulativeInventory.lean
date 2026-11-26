/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import PhyslibExt.FluidDynamics.Traffic.VehicleAccounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cumulative link inventory

## i. Overview

A link vehicle count updated at each step by the boundary
balance `N (j + 1) = N j + dt * (Fin j - Fout j)` telescopes
over any finite number of steps: the count is the initial
count plus cumulative arrivals minus cumulative departures,
with the initial count and both cumulative origins explicit.
This is aggregate conservation only; it does not assert FIFO
order or a delay formula. The final corollary supplies the
per-step balance from finite-cell vehicle accounting, where
the total change over a cell chain is the time step times the
difference of the two boundary fluxes.

## ii. Key results

- `FluidDynamics.Traffic.CumulativeInventory.cumulative_link_inventory`:
  inventory as initial count plus arrivals minus departures.
- `FluidDynamics.Traffic.CumulativeInventory.cumulative_link_inventory_sub`:
  the net change as one summed net inflow.
- `FluidDynamics.Traffic.CumulativeInventory.cumulative_inventory_vehicleAccounting`:
  the inventory identity for total counts in a finite cell
  chain under the conservative update.

## iii. Table of contents

- A. Cumulative inventory

## iv. References

- C. F. Daganzo, the cell transmission model, *Transp. Res.
  B* 28, 1994, and *Transp. Res. B* 29, 1995 (link vehicle
  counts from boundary flows).
-/

@[expose] public section

namespace FluidDynamics.Traffic.CumulativeInventory

/-! ## A. Cumulative inventory -/

/-- Cumulative vehicle inventory from per-step link balance.
If the vehicle count `N` evolves by
`N (j + 1) = N j + dt * (Fin j - Fout j)` at every step (the
finite-cell balance with boundary in/out fluxes), then after
`n` steps the count is the initial count plus cumulative
arrivals `∑ j < n, dt * Fin j` minus cumulative departures
`∑ j < n, dt * Fout j`, with both count origins explicit. No
FIFO or delay conclusion is asserted from aggregate
conservation. -/
theorem cumulative_link_inventory (N Fin Fout : ℕ → ℝ)
    (dt : ℝ) (hdt : 0 ≤ dt)
    (hstep : ∀ j, N (j + 1) = N j + dt * (Fin j - Fout j))
    (n : ℕ) :
    N n = N 0 + (∑ j ∈ Finset.range n, dt * Fin j)
      - ∑ j ∈ Finset.range n, dt * Fout j := by
  have _ := hdt
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hstep n, ih, Finset.sum_range_succ, Finset.sum_range_succ]
      ring

/-- The same inventory with the cumulative curves combined:
`N n - N 0` is the single summed net inflow. -/
theorem cumulative_link_inventory_sub (N Fin Fout : ℕ → ℝ)
    (dt : ℝ) (hdt : 0 ≤ dt)
    (hstep : ∀ j, N (j + 1) = N j + dt * (Fin j - Fout j))
    (n : ℕ) :
    N n - N 0
      = ∑ j ∈ Finset.range n, dt * (Fin j - Fout j) := by
  have h := cumulative_link_inventory N Fin Fout dt hdt hstep n
  have hsum : (∑ j ∈ Finset.range n, dt * (Fin j - Fout j))
      = (∑ j ∈ Finset.range n, dt * Fin j)
        - ∑ j ∈ Finset.range n, dt * Fout j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, h]
  ring

/-- Cumulative inventory for the total vehicle count of a
finite cell chain. If densities `k j i` evolve by the
conservative update
`k (j + 1) i = k j i + dt / dx * (F j i - F j (i + 1))` with
face fluxes `F j`, then after `nSteps` steps the total count
`∑ i, dx * k nSteps i` is the initial total plus cumulative
boundary arrivals `∑ j, dt * F j 0` minus cumulative boundary
departures `∑ j, dt * F j nCells`. The per-step total change
is the vehicle-accounting identity. -/
theorem cumulative_inventory_vehicleAccounting {nCells nSteps : ℕ}
    (k F : ℕ → ℕ → ℝ) (dt dx : ℝ) (hdt : 0 ≤ dt) (hdx : 0 < dx)
    (hupdate : ∀ j i, k (j + 1) i
      = k j i + dt / dx * (F j i - F j (i + 1))) :
    (∑ i ∈ Finset.range nCells, dx * k nSteps i)
      = (∑ i ∈ Finset.range nCells, dx * k 0 i)
        + (∑ j ∈ Finset.range nSteps, dt * F j 0)
        - ∑ j ∈ Finset.range nSteps, dt * F j nCells := by
  refine cumulative_link_inventory
    (fun j => ∑ i ∈ Finset.range nCells, dx * k j i)
    (fun j => F j 0) (fun j => F j nCells) dt hdt ?_ nSteps
  intro j
  have hchange :=
    FluidDynamics.Traffic.VehicleAccounting.total_vehicle_change
      (k j) (F j) dt dx hdx (n := nCells)
  have hterm : (∑ i ∈ Finset.range nCells, dx * (k (j + 1) i - k j i))
      = dt * (F j 0 - F j nCells) := by
    have hcong : (∑ i ∈ Finset.range nCells, dx * (k (j + 1) i - k j i))
        = ∑ i ∈ Finset.range nCells,
          dx * ((k j i + dt / dx * (F j i - F j (i + 1))) - k j i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hupdate j i]
    rw [hcong]
    exact hchange
  have hdiff : (∑ i ∈ Finset.range nCells, dx * k (j + 1) i)
      - ∑ i ∈ Finset.range nCells, dx * k j i
      = dt * (F j 0 - F j nCells) := by
    rw [← hterm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  linarith [hdiff]

end FluidDynamics.Traffic.CumulativeInventory
