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
