/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.MoserWormCover.HalfSemidisk

/-! # Tests for the half-disk covering theorem -/

open MoserConvexWormCoverConstant

example : CoversEveryUnitArc halfSemidisk := halfSemidiskCovers_holds

-- In any placement of the straight unit arc, both endpoints must lie on the diameter.
example (angle : ℝ) (c : ℂ)
    (h : ∀ t, move angle c (straightUnitArc.path t) ∈ halfSemidisk) :
    (move angle c (straightUnitArc.path 0)).im = 0 ∧
      (move angle c (straightUnitArc.path 1)).im = 0 := by
  let a := move angle c (straightUnitArc.path 0)
  let b := move angle c (straightUnitArc.path 1)
  obtain ⟨ha, haim⟩ : ‖a‖ ≤ 1 / 2 ∧ 0 ≤ a.im := h 0
  obtain ⟨hb, hbim⟩ : ‖b‖ ≤ 1 / 2 ∧ 0 ≤ b.im := h 1
  have hd : ‖a - b‖ = 1 := by
    rw [← dist_eq_norm, (move_isometry angle c).dist_eq]
    simp [straightUnitArc, straightPath, Complex.dist_eq]
  have hsum : a + b = 0 := by
    apply norm_eq_zero.mp
    nlinarith [parallelogram_law_with_norm ℝ a b,
      sq_le_sq' (by linarith [norm_nonneg a]) ha, sq_le_sq' (by linarith [norm_nonneg b]) hb]
  have him : a.im + b.im = 0 := by simpa using congrArg Complex.im hsum
  change a.im = 0 ∧ b.im = 0
  constructor <;> linarith
