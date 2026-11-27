/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LonelyMarriageableStrictGrowth

open MetaMathlibExt

-- Both strict inequalities hold at the first index in their respective ranges.
example : lonelySinglesCount 2 < lonelySinglesCount 3 :=
  lonely_marriageable_strictMono.1 2 (by decide)

example : marriageableSinglesCount 3 < marriageableSinglesCount 4 :=
  lonely_marriageable_strictMono.2 3 (by decide)

-- The counts on either side of the preceding step are equal, so the ranges cannot be extended.
example : lonelySinglesCount 1 = lonelySinglesCount 2 ∧
    marriageableSinglesCount 2 = marriageableSinglesCount 3 := by
  decide +kernel

-- The two base sizes have no marriageable inputs to the three extra families.
example : 1 ≤ marriageableSinglesCount 2 := by
  simpa [NoncrossingPartition.card_zero, marriageableSinglesCount_of_le_one (n := 0) (by decide)]
    using card_add_three_mul_marriageable_le 0

example : 1 ≤ marriageableSinglesCount 3 := by
  simpa [NoncrossingPartition.card_one, marriageableSinglesCount_of_le_one (n := 1) (by decide)]
    using card_add_three_mul_marriageable_le 1

-- At n = 2 all four families are already needed.
example : 5 ≤ marriageableSinglesCount 4 := by
  have h : marriageableSinglesCount 2 = 1 := by decide +kernel
  simpa [NoncrossingPartition.card_two, h] using card_add_three_mul_marriageable_le 2
