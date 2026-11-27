/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HockeyStickLatticeSequences

/-! # Tests for the cardinality of labeled lattice sequences -/

open MetaMathlibExt

-- Width zero leaves just the two prescribed endpoints.
example : (latticeSequences 0 2).card = 1 := by decide

-- The empty composition at k = 0 leaves no labels or positive lattice entries.
example : (labeledTableaux [] 0 ×ˢ latticeSequences 1 0).card = 1 := by
  have ha : ([] : List ℕ) ∈ hockeyCompositions 0 0 := by decide
  exact (card_labeledLatticeSequences (k := 0) (n := 0) (r := 0) (α := []) (hα := ha)).trans
    (by decide)

-- Two possible row labels and nine possible positions of the single rise.
example : (labeledTableaux [2] 2 ×ˢ latticeSequences 8 1).card = 18 := by
  have ha : ([2] : List ℕ) ∈ hockeyCompositions 3 2 := by decide
  exact (card_labeledLatticeSequences (k := 3) (n := 0) (r := 2) (α := [2]) (hα := ha)).trans
    (by decide)
