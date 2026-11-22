/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import PhyslibExt.FluidDynamics.Traffic.CumulativeInventory

/-!
# Cumulative inventory checks

Focused checks for
`PhyslibExt.FluidDynamics.Traffic.CumulativeInventory`: three
steps from a nonzero initial count with constant boundary
fluxes, three steps with zero arrivals, and the total count
of a one-cell chain under the conservative update for two
steps.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic.CumulativeInventory

/-- Three steps from five initial vehicles with arrival flux
`3`, departure flux `1`, and `dt = 2` give `5 + 18 - 6 = 17`. -/
example (N : ℕ → ℝ) (h0 : N 0 = 5)
    (hstep : ∀ j, N (j + 1) = N j + 2 * ((3 : ℝ) - 1)) :
    N 3 = 17 := by
  have h := cumulative_link_inventory N (fun _ => (3 : ℝ))
    (fun _ => (1 : ℝ)) 2 (by norm_num) hstep 3
  norm_num [Finset.sum_range_succ, h0] at h
  linarith [h]

/-- With zero subsequent arrivals, ten initial vehicles and
departure flux `2` at `dt = 1` leave `10 - 6 = 4` after three
steps. -/
example (N : ℕ → ℝ) (h0 : N 0 = 10)
    (hstep : ∀ j, N (j + 1) = N j + 1 * ((0 : ℝ) - 2)) :
    N 3 = 4 := by
  have h := cumulative_link_inventory N (fun _ => (0 : ℝ))
    (fun _ => (2 : ℝ)) 1 (by norm_num) hstep 3
  norm_num [Finset.sum_range_succ, h0] at h
  linarith [h]

/-- One-cell chain corollary over two steps: the total count
is the initial total plus two arrival terms minus two
departure terms. -/
example (k F : ℕ → ℕ → ℝ) (dt dx : ℝ) (hdt : 0 ≤ dt)
    (hdx : 0 < dx)
    (hupdate : ∀ j i, k (j + 1) i
      = k j i + dt / dx * (F j i - F j (i + 1))) :
    (∑ i ∈ Finset.range 1, dx * k 2 i)
      = (∑ i ∈ Finset.range 1, dx * k 0 i)
        + (dt * F 0 0 + dt * F 1 0)
        - (dt * F 0 1 + dt * F 1 1) := by
  have h := cumulative_inventory_vehicleAccounting
    (nCells := 1) (nSteps := 2) k F dt dx hdt hdx hupdate
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith [h]
