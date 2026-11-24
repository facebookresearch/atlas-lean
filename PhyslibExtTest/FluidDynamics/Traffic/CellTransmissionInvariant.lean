/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.Traffic.CellTransmissionInvariant
import Mathlib.Tactic.NormNum

/-!
# Cell-transmission invariance checks

Focused checks for
`PhyslibExt.FluidDynamics.Traffic.CellTransmissionInvariant`: with
`kj = v = w = 1` and `dt / dx = 1`, a cell at density 0 with a full
upstream cell updates to density `1 / 2` (checked through the
interval membership), and a full cell stays admissible.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic.CellTransmission

/-- Update of an empty cell below a full cell: value `1 / 2`. -/
example : (0 : ℝ) + (1 / 1) * (faceFlux 1 1 1 1 0
    - faceFlux 1 1 1 0 0) = 1 / 2 := by
  have hcap : capacity (1 : ℝ) 1 1 = 1 / 2 := by norm_num [capacity]
  have hf1 : faceFlux (1 : ℝ) 1 1 1 0 = 1 / 2 := by
    simp only [faceFlux, demand, supply, hcap]
    norm_num
  have hf0 : faceFlux (1 : ℝ) 1 1 0 0 = 0 := by
    simp only [faceFlux, demand, supply, hcap]
    norm_num
  rw [hf1, hf0]
  norm_num

/-- The updated density stays in `[0, 1]` by the invariant. -/
example : 0 ≤ (1 : ℝ) + (1 / 1) * (faceFlux 1 1 1 0 1
    - faceFlux 1 1 1 1 1)
    ∧ (1 : ℝ) + (1 / 1) * (faceFlux 1 1 1 0 1
    - faceFlux 1 1 1 1 1) ≤ 1 :=
  update_mem_Icc (by norm_num) (by norm_num) (by norm_num)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num)
    (by norm_num)
