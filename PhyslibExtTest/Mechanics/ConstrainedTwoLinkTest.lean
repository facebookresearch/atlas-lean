/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.ConstrainedTwoLink
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Two-link pendulum checks

Concrete consumers of `PhyslibExt.Mechanics.ConstrainedTwoLink`: noncollinear links with nonzero
angular velocities, stretched and folded collinear links, the zero-length boundary, and the main
lemmas applied to those parameters and to a uniformly rotating trajectory.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Fixtures
- B. The main lemmas on the fixture parameters

## iv. References

None.
-/

namespace PhyslibExtTest.Mechanics.ConstrainedTwoLink

open PhyslibExt.Mechanics.ConstrainedTwoLink
open scoped Matrix

/-! ## A. Fixtures -/

/-- Noncollinear links and nonzero angular velocities: `m₁ = 2`, `m₂ = 1`, `l₁ = 1`, `l₂ = 2`,
`q = (π / 3, 0)`, `w = (1, 1)`. The Cartesian velocities are `(1 / 2, √3 / 2)` and
`(5 / 2, √3 / 2)`, the kinetic energy is `9 / 2` and the determinant is `11`. -/
example :
    vel₁ 1 (Real.pi / 3) 1 = !₂[1 / 2, Real.sqrt 3 / 2] ∧
      vel₂ 1 2 (Real.pi / 3) 0 1 1 = !₂[5 / 2, Real.sqrt 3 / 2] ∧
      kineticEnergy 2 1 1 2 (Real.pi / 3) 0 1 1 = 9 / 2 ∧
      (massMatrix 2 1 1 2 (Real.pi / 3) 0).det = 11 := by
  have c3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have s3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [vel₁, c3, s3]
  · simp only [vel₂, vel₁, c3, s3, Real.cos_zero, Real.sin_zero]
    ext i; fin_cases i <;> simp; ring
  · rw [kineticEnergy_eq_massMatrix]
    simp only [Matrix.mulVec_apply_eq_sum, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    simp [massMatrix, Real.cos_pi_div_three]
    norm_num
  · have hs : Real.sin (Real.pi / 3 - 0) ^ 2 = 3 / 4 := by
      rw [sub_zero]
      exact Real.sq_sin_pi_div_three
    rw [massMatrix_det, hs]
    norm_num

/-- Collinear links stay regular: hanging straight (`q = (0, 0)`) and folded (`q = (0, π)`) the
determinant is `m₁ m₂ l₁² l₂² = 8`, and the counter-rotating velocity `w = (1, -1)` of the
stretched pendulum has kinetic energy `3 / 2`. -/
example :
    (massMatrix 2 1 1 2 0 0).det = 8 ∧ (massMatrix 2 1 1 2 0 Real.pi).det = 8 ∧
      kineticEnergy 2 1 1 2 0 0 1 (-1) = 3 / 2 := by
  have h00 : Real.sin ((0 : ℝ) - 0) = 0 := by rw [sub_self, Real.sin_zero]
  have h0pi : Real.sin ((0 : ℝ) - Real.pi) = 0 := by
    rw [zero_sub, Real.sin_neg, Real.sin_pi, neg_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [massMatrix_det_of_collinear h00]
    norm_num
  · rw [massMatrix_det_of_collinear h0pi]
    norm_num
  · rw [kineticEnergy_eq_massMatrix]
    simp only [Matrix.mulVec_apply_eq_sum, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    simp [massMatrix]
    norm_num

/-- Zero length is the invalid boundary: with `l₂ = 0` the determinant vanishes and the nonzero
angular velocity `w = (0, 1)` carries no kinetic energy. -/
example :
    (massMatrix 2 1 1 0 (Real.pi / 3) 0).det = 0 ∧
      kineticEnergy 2 1 1 0 (Real.pi / 3) 0 0 1 = 0 := by
  refine ⟨?_, ?_⟩
  · exact massMatrix_det_eq_zero_of_length_eq_zero (Or.inr rfl) 2 1 _ _
  · have hv₁ : vel₁ 1 (Real.pi / 3) 0 = 0 := by simp [vel₁]
    have hv₂ : vel₂ 1 0 (Real.pi / 3) 0 0 1 = 0 := by simp [vel₂, hv₁]
    simp [kineticEnergy, hv₁, hv₂]

/-! ## B. The main lemmas on the fixture parameters -/

/-- The rod constraints on the noncollinear fixture configuration. -/
example : ‖pos₁ 1 (Real.pi / 3)‖ = 1 ∧ ‖pos₂ 1 2 (Real.pi / 3) 0 - pos₁ 1 (Real.pi / 3)‖ = 2 :=
  pos_rod_constraints (by norm_num) (by norm_num) _ _

/-- The fixture masses and lengths give a positive determinant and a positive kinetic energy for
the counter-rotating velocity of the stretched pendulum. -/
example : 0 < (massMatrix 2 1 1 2 (Real.pi / 3) 0).det ∧ 0 < kineticEnergy 2 1 1 2 0 0 1 (-1) :=
  ⟨massMatrix_det_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _,
    kineticEnergy_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _
      (Or.inl one_ne_zero)⟩

/-- The uniformly rotating trajectory `q₁ s = π / 3 + s`, `q₂ s = s` meets the hypotheses of
`kineticEnergy_actual` at `t = 0`; its actual kinetic energy is `9 / 2`. -/
example : 2 * ‖deriv (fun s => pos₁ 1 (Real.pi / 3 + s)) 0‖ ^ 2 / 2 +
    1 * ‖deriv (fun s => pos₂ 1 2 (Real.pi / 3 + s) s) 0‖ ^ 2 / 2 = 9 / 2 := by
  have h₁ : HasDerivAt (fun s : ℝ => Real.pi / 3 + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (Real.pi / 3)
  have h := kineticEnergy_actual 2 1 1 2 h₁ (hasDerivAt_id' 0)
  simp only [add_zero] at h
  rw [h]
  simp only [Matrix.mulVec_apply_eq_sum, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp [massMatrix, Real.cos_pi_div_three]
  norm_num

end PhyslibExtTest.Mechanics.ConstrainedTwoLink
