/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GridReflectionTilings

/-! # Tests for reflection-fixed tilings of odd-width grids -/

namespace MetaMathlibExt

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

end MetaMathlibExt
