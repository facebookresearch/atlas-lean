/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AscentToDescentRearrangement

/-! # Tests for the ascent-to-descent rearrangement -/

namespace MetaMathlibExt.ascList_eq_desList_ascentToDescentRearrangement

private def descents (x : List ℕ) : Finset ℕ :=
  ((Finset.range (x.length - 1)).filter fun i => x.getD (i + 1) 0 < x.getD i 0).image (· + 1)

-- No adjacent pair contributes in an empty, singleton, or constant word.
example : descents (ascentToDescentRearrangement []) = ∅ ∧
    descents (ascentToDescentRearrangement [5]) = ∅ ∧
    descents (ascentToDescentRearrangement [2, 2, 2]) = ∅ := by decide

-- All maxima precede the minima. Both outer boundaries are ascents of the input.
example : descents (ascentToDescentRearrangement [2, 4, 4, 0, 0, 2]) = {1, 5} := by decide

-- A minimum precedes a maximum, and the intervening block has two different letters.
example : descents (ascentToDescentRearrangement [3, 0, 2, 1, 3, 0]) = {2, 4} := by
  unfold descents
  rw [← ascList_eq_desList_ascentToDescentRearrangement]
  decide

end MetaMathlibExt.ascList_eq_desList_ascentToDescentRearrangement
