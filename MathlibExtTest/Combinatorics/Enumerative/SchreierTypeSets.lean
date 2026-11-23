/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SchreierTypeSets

open MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

-- At the lower endpoint only the one-part partition remains.
example : refinedSchreierCount 2 1 = 0 := by decide

example : partitionMinPartCount 2 2 = 1 := by
  rw [partitionMinPartCount_eq_refined_add_one 2 1 (by decide)]
  decide

-- The partitions (3, 3), (4, 2), and (2, 2, 2) give three distinct refined sets.
example : IsRefinedSchreier 6 1 {3, 5, 7} ∧ IsRefinedSchreier 6 1 {5, 6, 7} ∧
    IsRefinedSchreier 6 1 {4, 5, 6, 7} := by decide

-- Sparsity alone allows unequal final gaps.
example : IsSparse {3, 4, 7} ∧ ¬IsRefinedSchreier 6 1 {3, 4, 7} := by decide

-- With l = 0 every positive part is allowed.
example : refinedSchreierCount 4 0 = 4 := by decide
