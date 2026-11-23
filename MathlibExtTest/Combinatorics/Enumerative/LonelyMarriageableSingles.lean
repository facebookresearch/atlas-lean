/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LonelyMarriageableSingles

open MetaMathlibExt

-- The empty partition is lonely.
example : lonelySinglesCount 0 = 1 ∧ marriageableSinglesCount 0 = 0 := by decide

-- At size two the singleton blocks can merge, while the one-block partition is lonely.
example : lonelySinglesCount 2 = 1 ∧ marriageableSinglesCount 2 = 1 := by decide

example : 2 = lonelySinglesCount 2 + marriageableSinglesCount 2 := by
  simpa only [NoncrossingPartition.card_two] using
    card_noncrossingPartition_eq_lonely_add_marriageable 2
