/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FinCases
import MathlibExt.Combinatorics.Enumerative.PermutationWordleFirstCorrectThree

open MetaMathlibExt

-- Apply the count at the minimum length, where the square of the rotation is not a cycle.
example : Nat.card {π : Equiv.Perm (Fin 4) //
    PermWordleSolvedIn cyclicShiftStrategy π 3 ∧
      PermWordleFirstCorrectAt cyclicShiftStrategy π 3} = 1 := by
  apply card_solvedIn_three_firstCorrectAt_three 4 (by decide)
  · refine ⟨0, by decide, ?_⟩
    intro i _
    fin_cases i
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨3, by decide⟩
  · decide

-- With five positions the inverse square differs from the forward square.
-- The secret [3, 4, 0, 1, 2] has no matches in either of the first two guesses.
example :
    let π := finRotate 5 ^ 3
    let g := permWordleGuess cyclicShiftStrategy π
    (∀ i, g 0 i ≠ π i) ∧ (∀ i, g 1 i ≠ π i) ∧ (∀ i, g 2 i = π i) := by
  intro π g
  have h₁ : g 1 = ⇑(finRotate 5).symm :=
    permWordleGuess_one_of_forall_ne cyclicShiftStrategy π (by decide)
  rw [h₁]
  refine ⟨by decide, by decide, ?_⟩
  change ∀ i, permWordleNextGuess cyclicShiftStrategy π (g 1) i = π i
  rw [h₁]
  let I := Finset.univ.filter fun i => (finRotate 5).symm i ≠ π i
  have hI : I = Finset.univ := by decide
  change ∀ i, permuteAlong I rfl (finRotate I.card) (finRotate 5).symm i = π i
  rw [hI]
  change ∀ i, permuteAlong Finset.univ (show (Finset.univ : Finset (Fin 5)).card = 5 by decide)
    (finRotate 5) (finRotate 5).symm i = π i
  rw [permuteAlong_univ]
  decide
