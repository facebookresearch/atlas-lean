/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.Transport.Traffic.CellTransmission

/-!
# Cell-transmission checks

Focused checks for `PhyslibExt.Transport.Traffic.CellTransmission`:
unit parameters with both densities `1 / 2` give face flux `1 / 2`;
a jammed downstream cell and zero capacity give flux `0`.

These are elaboration and non-vacuity checks, not new results.
-/

open CellTransmission

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

/-- Capacity is attained at the critical density `1 / 2` for unit
parameters, through the public theorem. -/
example : demand 1 1 1 (1 / 2) = capacity 1 1 1
    ∧ supply 1 1 1 (1 / 2) = capacity 1 1 1 :=
  capacity_attained (by norm_num) (by norm_num)

/-- Jammed receiving cell gives flux `0`, by computation. -/
example : faceFlux 1 1 1 (1 / 2) 1 = 0 := by
  norm_num [faceFlux, demand, supply, capacity]
