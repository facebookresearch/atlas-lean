/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HockeyStickTableauCardinality

/-! # Tests for the cardinality of labeled tableaux -/

open MetaMathlibExt

-- There is one empty labeling, even with no labels available.
example : (labeledTableaux [] 0).card = 1 := by
  rw [card_labeledTableaux]
  decide

-- The row choices give distinct nontrivial factors: C(4, 1) and C(4, 2).
example : (labeledTableaux [2, 3] 4).card = 24 := by
  rw [card_labeledTableaux]
  decide

-- If a row needs more labels than are available, there is no labeling.
example : (labeledTableaux [2, 4] 2).card = 0 := by
  rw [card_labeledTableaux]
  decide
