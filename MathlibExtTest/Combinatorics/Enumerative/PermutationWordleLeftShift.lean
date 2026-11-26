/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PermutationWordleLeftShift

open MetaMathlibExt

-- At the minimum length the two possibilities miss opposite pairs of positions.
example :
    Nat.card {π : Equiv.Perm (Fin 4) //
      PermWordleSolvedIn (cyclicShiftLeftStrategy 4) π 3 ∧
        PermWordleFirstCorrectAt (cyclicShiftLeftStrategy 4) π 2} = 2 :=
  card_solvedIn_three_firstCorrectAt_two_cyclicShiftLeft 4 (by decide)

-- For the secret [1, 0, 3, 2], the second guess is correct at positions 0 and 2,
-- and shifting the entries on the remaining positions finishes the game.
example :
    let π : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
    let g := permWordleGuess (cyclicShiftLeftStrategy 4) π
    (∀ i, g 0 i ≠ π i) ∧ (∀ i, g 1 i = π i ↔ i = 0 ∨ i = 2) ∧ g 2 = ⇑π := by
  intro π g
  have h₂ : g 1 = ⇑(finRotate 4) := by
    rw [show g 1 = _ from permWordleGuess_one_of_forall_ne _ π (by decide),
      cyclicShiftLeftStrategy_self, Equiv.symm_symm]
  refine ⟨by decide, ?_, ?_⟩
  · rw [h₂]
    decide
  · change permWordleNextGuess _ π (g 1) = ⇑π
    rw [h₂]
    let I := Finset.univ.filter fun i => finRotate 4 i ≠ π i
    have hI : I = {1, 3} := by decide
    have hs : I.sort = [1, 3] := by
      rw [hI, Finset.sort_insert _ (by decide) (by decide), Finset.sort_singleton]
    change permuteAlong I rfl (cyclicShiftLeftStrategy 4 I.card) _ = _
    funext i
    by_cases hi : i ∈ I
    · simp only [permuteAlong, dite_eq_left hi, Finset.coe_orderIsoOfFin_apply,
        Finset.orderEmbOfFin_apply]
      have hc : I.card = 2 := by decide
      rw [cyclicShiftLeftStrategy_of_ne (by omega), finRotate_symm_apply]
      have hm : i = 1 ∨ i = 3 := by simpa [hI] using hi
      rcases hm with rfl | rfl <;>
        simp [Fin.sub_def, Finset.orderIsoOfFin_symm_apply, hs, hc, π] <;> decide
    · simpa [permuteAlong, hi] using (show finRotate 4 i = π i by simpa [I] using hi)
