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

-- The six rearrangements of two zeros and two twos give six distinct images.
-- This includes both split rules and an ordered middle block with both extremes.
example : ([[0, 0, 2, 2], [0, 2, 0, 2], [0, 2, 2, 0], [2, 0, 0, 2], [2, 0, 2, 0],
    [2, 2, 0, 0]].map ascentToDescentRearrangement).Nodup := by decide

-- The suffix originally contains a maximum followed by minima. After rearranging,
-- it has both extremes but contains no later maximum followed by a minimum.
example : ascentToDescentRearrangement [0, 2, 1, 2, 0, 0] = [2, 0, 1, 0, 0, 2] := by decide

example : ascentToDescentRearrangement [] = [] ∧ ascentToDescentRearrangement [5] = [5] ∧
    ascentToDescentRearrangement [2, 2, 2, 2] = [2, 2, 2, 2] := by decide

-- Client of the public theorem: [0, 2, 0, 2] is the only preimage of this output.
example (x : List ℕ) (hx : ascentToDescentRearrangement x = [2, 0, 2, 0]) :
    x = [0, 2, 0, 2] :=
  ascentToDescentRearrangement_injective (hx.trans (by decide))

end MetaMathlibExt.ascList_eq_desList_ascentToDescentRearrangement
