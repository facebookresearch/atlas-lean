/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.HydraulicJumpEnergy
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hydraulic-jump energy checks

Focused checks for `PhyslibExt.EarthScience.HydraulicJumpEnergy`:
depths 1 and 2 with `q ^ 2 = 3 * g` are conjugate and give energy
loss `1 / 8`; the reverse orientation gives `-1 / 8`.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Conjugate fixture: equal specific force at depths 1 and 2. -/
example : rectangularSpecificForce (Real.sqrt 3) 1 1
    = rectangularSpecificForce (Real.sqrt 3) 1 2 := by
  simp [rectangularSpecificForce]
  norm_num

/-- Energy loss `1 / 8` at the conjugate fixture. -/
example : rectangularSpecificEnergy (Real.sqrt 3) 1 1
    - rectangularSpecificEnergy (Real.sqrt 3) 1 2 = 1 / 8 := by
  have hM : rectangularSpecificForce (Real.sqrt 3) 1 1
      = rectangularSpecificForce (Real.sqrt 3) 1 2 := by
    simp [rectangularSpecificForce]
    norm_num
  rw [specific_energy_jump_loss (by norm_num) (by norm_num)
    (by norm_num) hM]
  norm_num

/-- Reverse orientation: the loss changes sign. -/
example : rectangularSpecificEnergy (Real.sqrt 3) 1 2
    - rectangularSpecificEnergy (Real.sqrt 3) 1 1 = -1 / 8 := by
  have hM : rectangularSpecificForce (Real.sqrt 3) 1 2
      = rectangularSpecificForce (Real.sqrt 3) 1 1 := by
    simp [rectangularSpecificForce]
    norm_num
  rw [specific_energy_jump_loss (by norm_num) (by norm_num)
    (by norm_num) hM]
  norm_num

/-- Positivity of the loss at the conjugate fixture. -/
example : 0 < rectangularSpecificEnergy (Real.sqrt 3) 1 1
    - rectangularSpecificEnergy (Real.sqrt 3) 1 2 := by
  have hM : rectangularSpecificForce (Real.sqrt 3) 1 1
      = rectangularSpecificForce (Real.sqrt 3) 1 2 := by
    simp [rectangularSpecificForce]
    norm_num
  exact specific_energy_jump_loss_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hM
