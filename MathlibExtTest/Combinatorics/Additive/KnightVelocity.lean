/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.KnightVelocity
import Mathlib.Tactic.NormNum

/-! # Tests for generalized knight velocity -/

open MetaMathlibExt Filter
open scoped BigOperators

-- The centered square includes its corners and excludes points just outside.
example : (2, -2) ∈ maxNormBall 2 ∧ (2, -3) ∉ maxNormBall 2 := by decide

example : maxNormBall 0 = {(0, 0)} := by simp [maxNormBall]

example : (maxNormBall 2).card = 25 := by norm_num [card_maxNormBall]

-- The ordinary knight has the advertised velocity relative to the king.
example : Tendsto
    (fun h : ℕ => (2 * (h : ℝ) / 3) *
      (((∑ p ∈ maxNormBall h, (pieceDistance (knightMoves 1 2) p : ℝ)) /
        ((maxNormBall h).card : ℝ))⁻¹)) atTop (nhds (24 / 13 : ℝ)) := by
  have h := knight_velocity_formula 1 2 (by decide) (by decide) (by decide) ⟨1, rfl⟩
  norm_num at h ⊢
  exact h

-- A nonclassical knight checks that the limit depends on both move lengths.
example : Tendsto
    (fun h : ℕ => (2 * (h : ℝ) / 3) *
      (((∑ p ∈ maxNormBall h, (pieceDistance (knightMoves 2 3) p : ℝ)) /
        ((maxNormBall h).card : ℝ))⁻¹)) atTop (nhds (90 / 31 : ℝ)) := by
  have h := knight_velocity_formula 2 3 (by decide) (by decide) (by decide) ⟨2, rfl⟩
  norm_num at h ⊢
  exact h
