/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.WeightedFilePlacements

open MetaMathlibExt

-- The empty placement is the unique contribution on the empty board.
example (m : ℕ) : weightedFileNumber m [] 0 = 1 := by
  have hempty : filePlacements [] = {∅} := by decide
  simp [weightedFileNumber, hempty, Finset.filter_singleton, filePlacementWeight]

-- The two full placements on the nonempty columns have weights -2 and 1.
example : weightedFileNumber 3 [0, 1, 2] 2 = -1 := by decide

example : ∑ k ∈ Finset.range 4,
    weightedFileNumber 3 [0, 1, 2] k * mFallingFactorial (-2) (3 - k) 3 = -48 := by
  exact (weightedFileNumber_factorization 3 (by decide) [0, 1, 2] (by decide) (-2)).trans
    (by decide)

-- The left column has only one cell in the chosen level, but the next column has both rows.
example : (filePlacementBlock 2 [1, 2] {(0, 0), (1, 1)} 0 (0, 0)).card = 2 := by
  decide

-- The leftmost cell is fixed on the top row; the other two cells vary independently.
example : (filePlacementBlock 2 [2, 2, 2] {(0, 1), (1, 0), (2, 0)} 0 (0, 1)).card = 4 := by
  decide

-- At level one, the outside cell and the leftmost cell of the level both stay fixed.
set_option maxRecDepth 4096 in
example : filePlacementBlock 2 [1, 4, 4] {(0, 0), (1, 3), (2, 2)} 1 (1, 3) =
    {{(0, 0), (1, 3), (2, 2)}, {(0, 0), (1, 3), (2, 3)}} := by
  decide
