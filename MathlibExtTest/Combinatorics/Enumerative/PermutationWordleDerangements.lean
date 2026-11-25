/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PermutationWordleDerangements

open MetaMathlibExt

-- At the lower bound there is exactly one qualifying secret.
example :
    Nat.card {π : Equiv.Perm (Fin 3) //
      (∀ i, π i ≠ i) ∧ PermWordleSolvedIn cyclicShiftStrategy π 3} = 1 :=
  card_derangements_solvedIn_three_cyclicShift 3 (by decide)

-- The forward rotation is that secret. Its second guess misses all three positions.
example : (∀ i, finRotate 3 i ≠ i) ∧ PermWordleSolvedIn cyclicShiftStrategy (finRotate 3) 3 := by
  have h₁ : permWordleGuess cyclicShiftStrategy (finRotate 3) 1 = ⇑(finRotate 3).symm :=
    permWordleGuess_one_of_forall_ne _ _ (by decide)
  have hall : (Finset.univ.filter fun i => (finRotate 3).symm i ≠ finRotate 3 i) = Finset.univ :=
    Finset.eq_univ_of_forall (by decide)
  refine ⟨by decide, by decide, ?_, ?_⟩
  · change permWordleGuess _ _ (1 + 1) = _
    rw [permWordleGuess_succ, h₁]
    change permuteAlong _ rfl (finRotate _) (finRotate 3).symm = _
    rw [hall]
    have rotate_all (m : ℕ) (hm : (Finset.univ : Finset (Fin 3)).card = m) (h : m = 3) :
        permuteAlong Finset.univ hm (finRotate m) (finRotate 3).symm = ⇑(finRotate 3) := by
      subst h
      rw [permuteAlong_univ]
      apply funext
      decide
    exact rotate_all _ rfl (by simp)
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · exact fun h => absurd (congrFun h 0) (by decide)
    · rw [h₁]
      exact fun h => absurd (congrFun h 0) (by decide)
