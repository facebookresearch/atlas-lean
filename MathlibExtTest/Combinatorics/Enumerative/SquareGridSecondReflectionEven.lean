/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SquareGridSecondReflectionEven

/-! # Tests for the second reflection of an even square grid -/

open MetaMathlibExt

-- Swapping the two designs fixes no design, but there are two reflected cell pairs.
example : fixedTilingCount (cellR2F 2 2) (Equiv.swap (0 : Fin 2) 1) = 4 := by
  rw [squareGrid_r2f_even 2 _ (by simp [sq]) (by decide)]
  decide

-- Independent enumeration checks the same count on the smallest positive even square.
example : fixedTilingCount (cellR2F 2 2) (Equiv.swap (0 : Fin 2) 1) = 4 := by decide

-- The 4 × 4 grid with the identity design permutation has eight reflected pairs.
example : fixedTilingCount (cellR2F 4 4) (1 : Equiv.Perm (Fin 3)) = 6561 := by
  rw [squareGrid_r2f_even 4 _ (one_pow 2) (by decide)]
  decide
