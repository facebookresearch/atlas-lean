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
