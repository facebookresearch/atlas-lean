/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PermutationWordleFirstCorrectTwo

open MetaMathlibExt

-- The public count at the minimum length.
example :
    Nat.card {π : Equiv.Perm (Fin 4) //
      PermWordleSolvedIn cyclicShiftStrategy π 3 ∧
        PermWordleFirstCorrectAt cyclicShiftStrategy π 2} = 6 :=
  card_solvedIn_three_firstCorrectAt_two_cyclicShift 4 (by decide)

-- The secret [1, 0, 3, 2] first agrees with the second guess at positions 1 and 3.
-- Rotating the entries at the other two positions then finishes the game.
example :
    let π : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
    let g := permWordleGuess cyclicShiftStrategy π
    (∀ i, g 0 i ≠ π i) ∧ (∀ i, g 1 i = π i ↔ i = 1 ∨ i = 3) ∧ g 2 = ⇑π := by
  intro π g
  have h₁ : g 1 = ⇑(finRotate 4).symm :=
    permWordleGuess_one_of_forall_ne cyclicShiftStrategy π (by decide)
  refine ⟨by decide, ?_, ?_⟩
  · rw [h₁]
    decide
  · change permWordleNextGuess cyclicShiftStrategy π (g 1) = ⇑π
    rw [h₁]
    let I := Finset.univ.filter fun i => (finRotate 4).symm i ≠ π i
    have hI : I = {0, 2} := by decide
    have hs : I.sort = [0, 2] := by
      rw [hI, Finset.sort_insert _ (by decide) (by decide), Finset.sort_singleton]
    change permuteAlong I rfl (finRotate I.card) _ = _
    funext i
    by_cases hi : i ∈ I
    · simp only [permuteAlong, dite_eq_left hi, Finset.coe_orderIsoOfFin_apply,
        Finset.orderEmbOfFin_apply]
      have hc : I.card = 2 := by decide
      rw [finRotate_symm_apply (n := I.card)]
      have hm : i = 0 ∨ i = 2 := by simpa [hI] using hi
      rcases hm with rfl | rfl <;>
        simp [Fin.sub_def, Finset.orderIsoOfFin_symm_apply, hs, hc, π] <;> decide
    · have hmiss : (finRotate 4).symm i = π i := by simpa [I] using hi
      simpa [permuteAlong, hi] using hmiss
