/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GridSecondReflectionTilings

/-! # Tests for tilings fixed by the second reflection -/

open MetaMathlibExt

-- Only the second coordinate changes.
example : cellR2F 3 4 (0, 1) = (0, 2) := by decide

-- Independently enumerate the tilings of one reflected pair with two swapped designs.
example : fixedTilingCount (cellR2F 1 2) (Equiv.swap (0 : Fin 2) 1) = 2 := by decide

-- The first side may be odd; each of the six pairs has two choices even with no fixed design.
example : fixedTilingCount (cellR2F 3 4) (Equiv.swap (0 : Fin 2) 1) = 64 := by
  rw [rectangularGrid_r2f_even 3 4 _ (by simp [sq]) (by decide)]
  decide

-- With no tile designs, there is no tiling even for the smallest even second side.
example : fixedTilingCount (cellR2F 1 2) (1 : Equiv.Perm (Fin 0)) = 0 := by
  rw [rectangularGrid_r2f_even 1 2 _ (by simp) (by decide)]
  decide
