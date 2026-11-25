/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.KnightVelocity

/-! # Tests for the knight velocity formula and the max-norm ball -/

open MetaMathlibExt

-- The ball of radius zero is the origin alone.
example : maxNormBall 0 = {(0, 0)} := by
  simp [maxNormBall]

-- Boundary points belong to the ball, points just outside do not.
example : (1, -1) ∈ maxNormBall 1 ∧ (2, 0) ∉ maxNormBall 1 := by
  simp [maxNormBall]

example : (maxNormBall 2).card = 25 := by
  rw [card_maxNormBall]
  norm_num

-- The usual knight is 24/13 times faster than the king.
example : Filter.Tendsto
    (fun h : ℕ => (2 * (h : ℝ) / 3) *
      (((∑ p ∈ maxNormBall h, (pieceDistance (knightMoves 1 2) p : ℝ)) /
        ((maxNormBall h).card : ℝ))⁻¹))
    Filter.atTop (nhds (24 / 13)) := by
  have h := knight_velocity_formula 1 2 le_rfl (by norm_num) (by decide) ⟨1, rfl⟩
  push_cast at h
  convert h using 2
  norm_num

-- The (2, 3)-knight: `2 (a + b) b² / (a² + 3 b²) = 90 / 31`.
example : Filter.Tendsto
    (fun h : ℕ => (2 * (h : ℝ) / 3) *
      (((∑ p ∈ maxNormBall h, (pieceDistance (knightMoves 2 3) p : ℝ)) /
        ((maxNormBall h).card : ℝ))⁻¹))
    Filter.atTop (nhds (90 / 31)) := by
  have h := knight_velocity_formula 2 3 (by norm_num) (by norm_num) (by decide) ⟨2, rfl⟩
  push_cast at h
  convert h using 2
  norm_num
