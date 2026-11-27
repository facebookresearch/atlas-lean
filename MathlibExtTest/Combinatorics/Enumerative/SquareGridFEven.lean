/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SquareGridFEven

/-! # Tests for reflection-fixed tilings of an even square grid -/

namespace MetaMathlibExt

-- The swap fixes no design, but each of the two reflected pairs has two choices.
example : fixedTilingCount (cellF 2 2) (Equiv.swap (0 : Fin 2) 1) = 4 := by
  rw [squareGrid_f_even 2 _ (by simp [sq]) (by decide)]
  decide

-- Check the same count directly from the definition on the smallest even square.
example : fixedTilingCount (cellF 2 2) (Equiv.swap (0 : Fin 2) 1) = 4 := by
  decide +kernel

-- The identity design permutation gives two choices for each of the eight pairs.
example : fixedTilingCount (cellF 4 4) (1 : Equiv.Perm (Fin 2)) = 256 := by
  rw [squareGrid_f_even 4 1 (one_pow 2) (by decide)]
  decide

end MetaMathlibExt
