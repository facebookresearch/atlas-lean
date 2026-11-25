/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.KnightDistance

/-! # Tests for generalized knight distance -/

open MetaMathlibExt Pointwise

-- Both coordinates are odd and the point lies on the negative boundary.
example : ∃ n : ℕ, n ≤ 39 ∧ (-5, -5) ∈ n • knightMoves 2 3 := by
  exact exists_knight_path_on_box (a := 2) (b := 3) (by decide) (by decide)
    (by decide) ⟨2, rfl⟩ (p := (-5, -5)) (by decide)

-- The zero-fold sumset contains the origin.
example : (0 : ℤ × ℤ) ∈ (0 : ℕ) • knightMoves 2 3 := by simp

-- At (12, 8) the sector inequality is an equality. At (12, 9) the strict
-- second sector applies, with a nonintegral leading term. The constant is shared.
example : ∃ M : ℝ,
    |(pieceDistance (knightMoves 2 3) (12, 8) : ℝ) - 12 / 3| ≤ M * 3 ∧
    |(pieceDistance (knightMoves 2 3) (12, 9) : ℝ) - (12 + 9) / (2 + 3)| ≤ M * 3 := by
  obtain ⟨M, hM⟩ := knight_distance_asymptotics
  have atPoint (y : ℤ) (hy : 0 ≤ y) (hyx : y ≤ 12) :=
    hM 2 3 12 y (by decide) (by decide) (by decide) ⟨2, rfl⟩ hy hyx
  refine ⟨M, ?_, ?_⟩
  · simpa only [Int.cast_ofNat, Nat.cast_ofNat] using (atPoint 8 (by decide) (by decide)).1 (by decide)
  · simpa only [Int.cast_ofNat, Nat.cast_ofNat] using (atPoint 9 (by decide) (by decide)).2 (by decide)
