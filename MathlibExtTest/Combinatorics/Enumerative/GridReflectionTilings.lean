/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GridReflectionTilings

/-! # Tests for reflection-fixed tilings of rectangular and square grids -/

namespace MetaMathlibExt

-- The swap fixes no design, but each of the six reflected pairs still has two choices.
example : fixedTilingCount (cellF 4 3) (Equiv.swap (0 : Fin 2) 1) = 64 := by
  rw [rectangularGrid_f_even 4 3 _ (by simp [sq]) (by decide)]
  decide

-- Even the smallest even-width grid needs a tile for its one reflected pair.
example : fixedTilingCount (cellF 2 1) (1 : Equiv.Perm (Fin 0)) = 0 := by
  decide

-- On a single column every cell has to carry a fixed tile.
example {T : Type*} [Fintype T] [DecidableEq T] (m : ℕ) [NeZero m]
    (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1) :
    fixedTilingCount (cellF 1 m) σ = tileFixedCount σ 1 ^ m := by
  simpa using rectangularGrid_f_odd 1 m σ hσ odd_one

-- Two reflected pairs have four choices each, and both center cells have two choices each.
example : fixedTilingCount (cellF 3 2) (Equiv.swap (0 : Fin 4) 1) = 64 := by
  rw [rectangularGrid_f_odd 3 2 _ (by simp [sq]) (by decide)]
  decide

-- A swap with no fixed tile cannot fill the center cell, even with tiles for the outer pair.
example : fixedTilingCount (cellF 3 1) (Equiv.swap (0 : Fin 2) 1) = 0 := by
  decide

-- On the one-cell square the tile must be fixed by the permutation.
example {T : Type*} [Fintype T] [DecidableEq T] (σ : Equiv.Perm T) (hσ : σ ^ 2 = 1) :
    fixedTilingCount (cellF 1 1) σ = tileFixedCount σ 1 := by
  simpa using squareGrid_f_odd 1 σ hσ odd_one

-- The three reflected pairs have four choices each; the three center cells have two each.
example : fixedTilingCount (cellF 3 3) (Equiv.swap (0 : Fin 4) 1) = 512 := by
  rw [squareGrid_f_odd 3 _ (by simp [sq]) (by decide)]
  decide

end MetaMathlibExt
