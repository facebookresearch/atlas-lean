/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.NonattackingBishopsAnassas

open MetaMathlibExt

-- The empty placement and the single white square are both counted.
example : bishopsSquare 0 0 = 1 := by decide
example : bishopsWhite 1 1 = 1 ∧ bishopsBlack 1 1 = 0 := by decide

-- Direct enumeration: the four legal pairs occupy a common row or a common column.
example : bishopsSquare 2 2 = 4 := by decide

-- The odd board has placements with four bishops; a fifth bishop is impossible.
example : bishopsSquare 3 4 = 8 := by
  rw [bishopsSquare_eq_sum]
  decide

example : bishopsSquare 3 5 = 0 := by
  rw [bishopsSquare_eq_sum]
  decide

-- The extension uses unsigned first-kind numbers for negative arguments.
example : extStirlingSecond (-1) (-3) = 2 ∧ extStirlingSecond 0 (-1) = 0 := by decide
