/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.BishopsArshonReindex

open MetaMathlibExt

-- Only the empty placement is possible on the empty board.
example : bishopsSquare 0 0 = 1 := by
  rw [bishopsSquare_eq_arshon]
  decide

-- In this case the second Stirling index is negative, not zero.
example : bishopsSquare 0 1 = 0 := by
  rw [bishopsSquare_eq_arshon]
  decide

-- On a 2 × 2 board the legal pairs share a row or a column.
example : bishopsSquare 2 2 = 4 := by
  rw [bishopsSquare_eq_arshon]
  decide

-- On a 3 × 3 board five pairs attack in each diagonal direction, leaving 26 legal pairs.
example : bishopsSquare 3 2 = 26 := by
  rw [bishopsSquare_eq_arshon]
  decide

-- Four bishops fit on the 3 × 3 board, but five do not.
example : bishopsSquare 3 4 = 8 := by
  rw [bishopsSquare_eq_arshon]
  decide

example : bishopsSquare 3 5 = 0 := by
  rw [bishopsSquare_eq_arshon]
  decide
