/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SquareGridR2Odd

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.SquareGridR2Odd` -/

namespace MetaMathlibExt

-- On the 3 × 3 grid with two designs and the identity design permutation, the four
-- half-turn pairs and the fixed centre cell give `2 ^ 4 * 2 = 32` fixed tilings.
example : fixedTilingCount (cellR2 3 3) (1 : Equiv.Perm (Fin 2)) = 32 := by
  rw [squareGrid_r2_odd 3 1 (one_pow 2) (by decide)]
  decide +kernel

-- The count agrees with a direct computation on the 3 × 3 grid.
example : fixedTilingCount (cellR2 3 3) (1 : Equiv.Perm (Fin 2)) = 32 := by
  decide +kernel

-- Swapping the two designs fixes no design, so on the 3 × 3 grid the centre cell
-- already rules out every tiling.
example : fixedTilingCount (cellR2 3 3) (Equiv.swap (0 : Fin 2) 1) = 0 := by
  decide +kernel

-- Edge case `n = 1`: the single cell is fixed by the half-turn, so the count is
-- the number of designs fixed by `σ`.
example {T : Type*} [Fintype T] [DecidableEq T] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1) :
    fixedTilingCount (cellR2 1 1) σ = tileFixedCount σ 1 := by
  rw [squareGrid_r2_odd 1 σ hσ odd_one]
  simp

-- Edge case of no tiles: a grid with at least one cell has no tiling at all.
example : fixedTilingCount (cellR2 3 3) (1 : Equiv.Perm Empty) = 0 := by
  rw [squareGrid_r2_odd 3 1 (one_pow 2) (by decide), Fintype.card_empty]
  decide

end MetaMathlibExt
