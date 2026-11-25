/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PositionalColoredCompositionChooseTwo

namespace MetaMathlibExt.PositionalColoredCompositionChooseTwoTest

private theorem compositionsOne : (Finset.univ : Finset (Composition 1)) =
    {Composition.ones 1} := by
  symm
  apply Finset.eq_univ_of_card
  rw [composition_card]
  decide

private theorem compositionsThree : (Finset.univ : Finset (Composition 3)) =
    {Composition.single 3 (by decide), ⟨[1, 2], by simp, rfl⟩,
      ⟨[2, 1], by simp, rfl⟩, Composition.ones 3} := by
  symm
  apply Finset.eq_univ_of_card
  rw [composition_card]
  decide

-- At the smallest admissible `k`, only the composition `(2)` of `2` has a color.
example : positionalColoredCompositionCount 2 1 1 = 1 := by
  rw [odd_eq_choose_two_colorCompositions 1 le_rfl]
  have h : (Finset.univ : Finset (Composition 2)) =
      {Composition.single 2 (by decide), Composition.ones 2} := by
    symm
    apply Finset.eq_univ_of_card
    rw [composition_card]
    decide
  rw [h]
  decide

-- Read backwards, the identity evaluates a sum over the eight compositions of `4` from the four
-- compositions of `3`, whose odd colored weights are `3`, `1`, `2` and `1`.
example : ∑ c : Composition 4, (c.blocks.map fun p => p.choose 2).prod = 7 := by
  rw [← odd_eq_choose_two_colorCompositions 3 (by decide)]
  simp only [positionalColoredCompositionCount, compositionsThree]
  decide

-- The hypothesis `1 ≤ k` cannot be dropped: the empty composition of `0` counts once, while the
-- only composition `(1)` of `1` has no color.
example : positionalColoredCompositionCount 2 1 0 ≠
    ∑ c : Composition (0 + 1), (c.blocks.map fun p => p.choose 2).prod := by
  rw [positionalColoredCompositionCount_zero, compositionsOne]
  decide

end MetaMathlibExt.PositionalColoredCompositionChooseTwoTest
