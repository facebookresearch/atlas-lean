/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.KnightDistance

/-! # Tests for bounded reachability by generalized knights -/

open MetaMathlibExt Pointwise

-- Both coordinates are odd and the point lies on the negative boundary.
example : ∃ n : ℕ, n ≤ 39 ∧ (-5, -5) ∈ n • knightMoves 2 3 := by
  exact exists_knight_path_on_box (a := 2) (b := 3) (by decide) (by decide)
    (by decide) ⟨2, rfl⟩ (p := (-5, -5)) (by decide)

-- The zero-fold sumset contains the origin.
example : (0 : ℤ × ℤ) ∈ (0 : ℕ) • knightMoves 2 3 := by simp
