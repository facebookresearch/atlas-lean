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
example : cellR2F 2 3 (1, 0) = (1, 2) := by decide

-- Independently enumerate the tilings: the middle cell has no fixed design.
example : fixedTilingCount (cellR2F 1 3) (Equiv.swap (0 : Fin 2) 1) = 0 := by decide

-- On a 2 × 3 grid there are two reflected pairs and two fixed cells.
-- With four designs and one swap, each pair has four choices and each fixed cell has two.
example : fixedTilingCount (cellR2F 2 3) (Equiv.swap (0 : Fin 4) 1) = 64 := by
  rw [rectangularGrid_r2f_odd 2 3 _ (by simp [sq]) (by decide)]
  decide

-- For second side one, both cells lie on the reflection axis.
example : fixedTilingCount (cellR2F 2 1) (Equiv.swap (0 : Fin 4) 1) = 4 := by
  rw [rectangularGrid_r2f_odd 2 1 _ (by simp [sq]) (by decide)]
  decide
