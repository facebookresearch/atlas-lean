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
read back through the kernel-span characterization. The frame
checks use a nonrigid axial/bending vector, unit positive
semidefiniteness, and a three-mode rigid combination.

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

/-- Nonrigid frame data has the factored energy value `419 / 2`
at `EA = 11`, `EI = 5`, `L = 2`. -/
example : (![1, 2, -1, 4, 0, 3] : Fin 6 → ℝ)
    ⬝ᵥ (frameStiffness 11 5 2 *ᵥ ![1, 2, -1, 4, 0, 3])
    = 419 / 2 := by
  rw [frameStiffness_quad_form_factor]
  norm_num

/-- Pure axial stretch has positive frame energy `11 / 2`. -/
example : (![0, 0, 0, 1, 0, 0] : Fin 6 → ℝ)
    ⬝ᵥ (frameStiffness 11 5 2 *ᵥ ![0, 0, 0, 1, 0, 0])
    = 11 / 2 := by
  rw [frameStiffness_quad_form_factor]
  norm_num

/-- The unit-data frame matrix is positive semidefinite. -/
example : (frameStiffness 1 1 1).PosSemidef :=
  frameStiffness_posSemidef (by norm_num) (by norm_num) (by norm_num)

/-- A combination of the three planar rigid modes is in the
frame kernel. -/
example : frameStiffness 11 5 2 *ᵥ
    ((3 : ℝ) • ![1, 0, 0, 1, 0, 0]
      + (2 : ℝ) • ![0, 1, 0, 0, 1, 0]
      + (-1 : ℝ) • ![0, 0, 1, 0, 2, 1]) = 0 :=
  (frameStiffness_mulVec_eq_zero_iff (by norm_num) (by norm_num)
    (by norm_num) _).2 ⟨3, 2, -1, rfl⟩
