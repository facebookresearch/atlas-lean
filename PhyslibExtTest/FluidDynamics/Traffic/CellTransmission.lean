/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.FluidDynamics.Traffic.CellTransmission

/-!
# Cell-transmission checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.CellTransmission`:
unit parameters with both densities `1 / 2` give face flux `1 / 2`;
a jammed downstream cell gives flux `0`, and capacity is attained at
the critical density.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic.CellTransmission

/-- Unit witness: capacity `1 / 2`, flux `1 / 2`, within both bounds. -/
example : faceFlux 1 1 1 (1 / 2) (1 / 2) = 1 / 2
    ∧ faceFlux 1 1 1 (1 / 2) (1 / 2) ≤ demand 1 1 1 (1 / 2)
    ∧ faceFlux 1 1 1 (1 / 2) (1 / 2) ≤ supply 1 1 1 (1 / 2) := by
  refine ⟨by norm_num [faceFlux, demand, supply, capacity],
    faceFlux_le_demand, faceFlux_le_supply⟩

/-- Nonnegativity through the public theorem. -/
example : 0 ≤ faceFlux 2 3 10 4 9 :=
  faceFlux_nonneg_of_le (by norm_num) (by norm_num) (by norm_num)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- Capacity is attained at the critical density for unit parameters,
through the public theorem. -/
example : demand 1 1 1 (1 * 1 / (1 + 1)) = capacity 1 1 1
    ∧ supply 1 1 1 (1 * 1 / (1 + 1)) = capacity 1 1 1 :=
  capacity_attained (v := 1) (w := 1) (kj := 1) (by norm_num) (by norm_num)
    (by norm_num)

/-- Jammed receiving cell gives flux `0`, by computation. -/
example : faceFlux 1 1 1 (1 / 2) 1 = 0 := by
  norm_num [faceFlux, demand, supply, capacity]
