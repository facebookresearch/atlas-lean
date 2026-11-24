/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PermutationWordle
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- At the minimum length, the second guess gets both positions right.
example :
    (∑ d ∈ Finset.univ.filter (fun d : Equiv.Perm (Fin 2) => ∀ k, d k ≠ k),
        ((Finset.univ.filter fun i => permWordleGuess cyclicShiftStrategy d 1 i = d i).card : ℚ)) /
      (Finset.univ.filter (fun d : Equiv.Perm (Fin 2) => ∀ k, d k ≠ k)).card = 2 := by
  rw [avg_card_correct_second_guess_derangements 2 (by decide) cyclicShiftStrategy (by decide)]
  norm_num

-- The two derangements of length three give opposite scores for the same strategy.
example :
    (Finset.univ.filter fun i =>
      permWordleGuess cyclicShiftStrategy (finRotate 3) 1 i = finRotate 3 i).card = 0 := by
  rw [permWordleGuess_one_of_forall_ne _ _ (by decide)]
  decide

example :
    (Finset.univ.filter fun i =>
      permWordleGuess cyclicShiftStrategy (finRotate 3).symm 1 i = (finRotate 3).symm i).card =
      3 := by
  rw [permWordleGuess_one_of_forall_ne _ _ (by decide)]
  decide
