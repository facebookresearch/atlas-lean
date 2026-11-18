/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.BeamStiffness
import Mathlib.Tactic.NormNum

/-!
# Beam-stiffness checks

Focused checks for `PhyslibExt.Mechanics.BeamStiffness`: a unit
tip deflection produces end force `12 * EI / L ^ 3` at the tip,
and rigid translation produces no end forces.

These are elaboration and non-vacuity checks, not new results.
-/

open Matrix

/-- Unit tip deflection: tip force entry is `12` at `EI = L = 1`. -/
example : (beamStiffness 1 1 *ᵥ ![0, 0, 1, 0]) 2 = 12 := by
  norm_num [beamStiffness, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Rigid translation has zero energy. -/
example : (![1, 0, 1, 0] : Fin 4 → ℝ) ⬝ᵥ (beamStiffness 1 1 *ᵥ ![1, 0, 1, 0]) = 0 := by
  rw [beamStiffness_mulVec_translation]
  simp
