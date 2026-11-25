/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PositionalColoredCompositions

namespace MetaMathlibExt.PositionalColoredCompositionsTest

private theorem compositionsTwo : (Finset.univ : Finset (Composition 2)) =
    {Composition.single 2 (by decide), Composition.ones 2} := by
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

-- The smallest admissible total also works when the modulus exceeds it.
example : positionalColoredCompositionCount 3 2 2 =
    positionalColoredCompositionCount 3 2 1 + positionalColoredCompositionCount 3 1 1 :=
  positionalColoredCompositionCount_succ 3 1 1 (by decide) (by decide) (by decide)

-- At modulus two the two summands differ, and the colored residue wraps to zero.
example : positionalColoredCompositionCount 2 2 3 = 5 := by
  rw [positionalColoredCompositionCount_succ 2 1 2 (by decide) (by decide) (by decide)]
  simp only [positionalColoredCompositionCount, compositionsTwo]
  decide

-- With every position colored, the two sides of the proposed recurrence differ.
example : positionalColoredCompositionCount 1 2 3 = 8 ∧
    positionalColoredCompositionCount 1 2 2 + positionalColoredCompositionCount 1 1 2 = 6 := by
  simp only [positionalColoredCompositionCount, compositionsTwo, compositionsThree]
  decide

end MetaMathlibExt.PositionalColoredCompositionsTest
