/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.FrameStiffnessGlobal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Global frame stiffness checks

Concrete consumers of
`PhyslibExt.Mechanics.FrameStiffnessGlobal`: the horizontal
element, the oblique rigid modes in the global kernel,
non-unit instantiations of the unconditional results, and
the sign/order controls for the transform.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Horizontal and oblique elements
- B. Sign and order controls

## iv. References

- `PhyslibExt.Mechanics.FrameStiffnessGlobal`
- `PhyslibExt.Mechanics.BeamStiffness`
-/

open Matrix

namespace PhyslibExtTest.Mechanics.FrameStiffnessGlobal

open Mechanics.EulerBernoulli

/-! ## A. Horizontal and oblique elements -/

/-- The horizontal transform is the identity. -/
example : frameRotation 1 0 = 1 := by
  unfold frameRotation
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- For a horizontal element the global stiffness is the
local stiffness. -/
example (EA EI L : ℝ) :
    frameStiffnessGlobal EA EI L 1 0 = frameStiffness EA EI L := by
  have hT : frameRotation 1 0 = 1 := by
    unfold frameRotation
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  unfold frameStiffnessGlobal
  rw [hT]
  simp

/-- The oblique global rigid rotation about end 1 is in the
global kernel (direction cosines `(3/5, 4/5)`, `L = 2`). -/
example : frameStiffnessGlobal 2 3 2 (3 / 5) (4 / 5)
      *ᵥ ![0, 0, 1, -2 * (4 / 5) * 1, 2 * (3 / 5) * 1, 1] = 0 := by
  rw [frameStiffnessGlobal_mulVec_eq_zero_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  refine ⟨0, 0, 1, ?_⟩
  rw [frameRotation_mulVec_globalRotation 2 (3 / 5) (4 / 5) 1 (by norm_num)]
  simp

/-- The oblique global translation is in the global kernel,
through its local translation combination. -/
example : frameStiffnessGlobal 2 3 2 (3 / 5) (4 / 5)
      *ᵥ ![5, -2, 0, 5, -2, 0] = 0 := by
  rw [frameStiffnessGlobal_mulVec_eq_zero_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  refine ⟨3 / 5 * 5 + 4 / 5 * -2, -(4 / 5) * 5 + 3 / 5 * -2, 0, ?_⟩
  rw [frameRotation_mulVec_globalTranslation (3 / 5) (4 / 5) 5 (-2)]
  simp

/-- Symmetry and semidefiniteness also hold at non-unit
`(c, s) = (2, 1)`: no unit-circle premise is hidden in the
unconditional statements. -/
example : (frameStiffnessGlobal 2 3 2 2 1)ᵀ
    = frameStiffnessGlobal 2 3 2 2 1 :=
  frameStiffnessGlobal_transpose 2 3 2 2 1

example : (frameStiffnessGlobal 2 3 2 2 1).PosSemidef :=
  frameStiffnessGlobal_posSemidef (by norm_num) (by norm_num) (by norm_num)

/-- Energy invariance at concrete data. -/
example : (![1, 2, 3, 4, 5, 6] : Fin 6 → ℝ)
      ⬝ᵥ (frameStiffnessGlobal 2 3 2 (3 / 5) (4 / 5)
        *ᵥ ![1, 2, 3, 4, 5, 6])
    = (frameRotation (3 / 5) (4 / 5) *ᵥ ![1, 2, 3, 4, 5, 6])
      ⬝ᵥ (frameStiffness 2 3 2
        *ᵥ (frameRotation (3 / 5) (4 / 5) *ᵥ ![1, 2, 3, 4, 5, 6])) :=
  frameStiffnessGlobal_quad_form 2 3 2 (3 / 5) (4 / 5) ![1, 2, 3, 4, 5, 6]

/-! ## B. Sign and order controls -/

/-- Without the unit-circle hypothesis the rotation-mode
identity fails: at `(c, s) = (2, 0)` the fifth coordinate is
`L c ^ 2 w = 4`, not `L w = 1`. -/
example : ¬ frameRotation 2 0 *ᵥ ![0, 0, 1, 0, 2, 1]
    = (1 : ℝ) • ![0, 0, 1, 0, 1, 1] := by
  intro h
  have h4 := congrFun h 4
  simp [frameRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_six] at h4
  norm_num at h4

/-- Wrong-sign offset: flipping the signs of the far-end
translation breaks the rotation-mode identity at the
oblique direction. -/
example : ¬ frameRotation (3 / 5) (4 / 5)
      *ᵥ ![0, 0, 1, 2 * (4 / 5), -(2 * (3 / 5)), 1]
    = (1 : ℝ) • ![0, 0, 1, 0, 2, 1] := by
  intro h
  have h4 := congrFun h 4
  simp [frameRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_six] at h4
  norm_num at h4

/-- Wrong-sign transform: `T(c, -s)` does not map the
global rotation mode to the local one. -/
example : ¬ frameRotation (3 / 5) (-(4 / 5))
      *ᵥ ![0, 0, 1, -(2 * (4 / 5)), 2 * (3 / 5), 1]
    = (1 : ℝ) • ![0, 0, 1, 0, 2, 1] := by
  intro h
  have h3 := congrFun h 3
  simp [frameRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_six] at h3
  norm_num at h3

/-- Transposed transform: `Tᵀ` used as the global-to-local
map does not give the local rotation mode. -/
example : ¬ (frameRotation (3 / 5) (4 / 5))ᵀ
      *ᵥ ![0, 0, 1, -(2 * (4 / 5)), 2 * (3 / 5), 1]
    = (1 : ℝ) • ![0, 0, 1, 0, 2, 1] := by
  intro h
  have h3 := congrFun h 3
  simp [frameRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_six] at h3
  norm_num at h3

/-- Transpose-order control: the `T K Tᵀ` congruence does
not annihilate the oblique global rotation mode. -/
example : ¬ ((frameRotation (3 / 5) (4 / 5)) * frameStiffness 2 3 2
      * (frameRotation (3 / 5) (4 / 5))ᵀ)
      *ᵥ ![0, 0, 1, -(2 * (4 / 5)), 2 * (3 / 5), 1] = 0 := by
  intro h
  have h0 := congrFun h 0
  simp [frameRotation, frameStiffness, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_six] at h0
  norm_num at h0

#print axioms Mechanics.EulerBernoulli.frameRotation_transpose_mul
#print axioms Mechanics.EulerBernoulli.frameRotation_mul_transpose
#print axioms Mechanics.EulerBernoulli.frameRotation_mulVec_round_trip
#print axioms Mechanics.EulerBernoulli.frameStiffnessGlobal_quad_form
#print axioms
  Mechanics.EulerBernoulli.frameRotation_mulVec_globalTranslation
#print axioms
  Mechanics.EulerBernoulli.frameRotation_mulVec_globalRotation
#print axioms Mechanics.EulerBernoulli.frameStiffnessGlobal_transpose
#print axioms Mechanics.EulerBernoulli.frameStiffnessGlobal_posSemidef
#print axioms
  Mechanics.EulerBernoulli.frameStiffnessGlobal_mulVec_eq_zero_iff

end PhyslibExtTest.Mechanics.FrameStiffnessGlobal
