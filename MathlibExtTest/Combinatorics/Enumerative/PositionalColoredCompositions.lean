/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PositionalColoredCompositions

namespace MetaMathlibExt.positionalColoredCompositionCount_succ

private theorem univ_two : (Finset.univ : Finset (Composition 2)) =
    {Composition.single 2 (by decide), Composition.ones 2} := by
  apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) _).symm
  rw [Finset.card_univ, composition_card]
  decide

private theorem univ_three : (Finset.univ : Finset (Composition 3)) =
    {Composition.single 3 (by decide), ⟨[1, 2], by simp, rfl⟩,
     ⟨[2, 1], by simp, rfl⟩, Composition.ones 3} := by
  apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) _).symm
  rw [Finset.card_univ, composition_card]
  decide

-- The lower endpoint already has both branches, with blocks [2] and [1, 1].
example : positionalColoredCompositionCount 2 2 2 =
    positionalColoredCompositionCount 2 2 1 + positionalColoredCompositionCount 2 1 1 :=
  positionalColoredCompositionCount_succ 2 1 1 (by decide) (by decide) (by decide)

-- At size three the two residue classes have different counts.
example : positionalColoredCompositionCount 2 2 3 = 5 ∧
    positionalColoredCompositionCount 2 1 3 = 7 := by
  unfold positionalColoredCompositionCount
  rw [univ_three]
  decide

-- The divisibility hypothesis excludes an actual failure of the recurrence.
example : positionalColoredCompositionCount 1 2 3 ≠
    positionalColoredCompositionCount 1 2 2 + positionalColoredCompositionCount 1 1 2 := by
  unfold positionalColoredCompositionCount
  rw [univ_two, univ_three]
  decide

end MetaMathlibExt.positionalColoredCompositionCount_succ
