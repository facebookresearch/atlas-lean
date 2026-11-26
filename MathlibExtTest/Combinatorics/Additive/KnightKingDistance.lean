/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.KnightKingDistance

/-! # King distances in different quadrants -/

open MetaMathlibExt

example : pieceDistance kingMoves (-3, 2) = 3 := by
  rw [pieceDistance_kingMoves]
  decide

example : pieceDistance kingMoves (1, -4) = 4 := by
  rw [pieceDistance_kingMoves]
  decide
