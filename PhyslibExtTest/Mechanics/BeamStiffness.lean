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
rigid translation produces no end forces, the factored energy
form is positive on a nonrigid tip deflection, the matrix is
positive semidefinite at unit data, and the rotation mode is
read back through the kernel-span characterization.

These are elaboration and non-vacuity checks, not new results.
-/

open Matrix Mechanics.EulerBernoulli

/-- Unit tip deflection: tip force entry is `12` at `EI = L = 1`. -/
example : (beamStiffness 1 1 *ᵥ ![0, 0, 1, 0]) 2 = 12 := by
  norm_num [beamStiffness, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Rigid translation has zero energy. -/
example : (![1, 0, 1, 0] : Fin 4 → ℝ) ⬝ᵥ (beamStiffness 1 1 *ᵥ ![1, 0, 1, 0]) = 0 := by
  rw [beamStiffness_mulVec_translation]
  simp

/-- Nonrigid unit tip deflection has energy value `12` from the
factored quadratic form. -/
example : (![0, 0, 1, 0] : Fin 4 → ℝ)
    ⬝ᵥ (beamStiffness 1 1 *ᵥ ![0, 0, 1, 0]) = 12 := by
  rw [beamStiffness_quad_form_factor]
  norm_num

/-- The unit-data stiffness matrix is positive semidefinite. -/
example : (beamStiffness 1 1).PosSemidef :=
  beamStiffness_posSemidef (by norm_num) (by norm_num)

/-- The rotation mode is read back as a rigid-span element. -/
example : ∃ a b : ℝ,
    (![0, 1, 2, 1] : Fin 4 → ℝ)
      = a • ![1, 0, 1, 0] + b • ![0, 1, 2, 1] :=
  (beamStiffness_mulVec_eq_zero_iff (by norm_num) (by norm_num)
    ![0, 1, 2, 1]).1 (beamStiffness_mulVec_rotation 5 2)
