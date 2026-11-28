/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Perm.ShuffleFactorization
import Mathlib.Tactic.FinCases

/-!
# Stable ties and an empty shuffle block

Labels (1,0,1) keep the equal first and last labels in input order. Secondary sorting with
labels (0,1,0) produces input indices (1,2,0). An empty left block leaves the original
permutation entirely in the block factor and gives the identity shuffle.
-/

noncomputable section

namespace StableShuffleBoundaryTests

open Equiv.Perm

private theorem sort_first :
    Tuple.sort (![1, 0, 1] : Fin 3 → ℕ) = Equiv.swap (0 : Fin 3) 1 := by
  apply Eq.symm
  apply Tuple.eq_sort_iff.mpr
  constructor <;> decide

private theorem sort_second :
    Tuple.sort (![0, 1, 0] : Fin 3 → ℕ) = Equiv.swap (1 : Fin 3) 2 := by
  apply Eq.symm
  apply Tuple.eq_sort_iff.mpr
  constructor <;> decide

example : Tuple.successiveStableLabels (![1, 0, 1] : Fin 3 → ℕ) ![0, 1, 0] =
    ![toLex (1, 1), toLex (0, 0), toLex (0, 1)] := by
  rw [Tuple.successiveStableLabels, sort_first]
  funext i
  fin_cases i <;> rfl

example : Tuple.sort
    (Tuple.successiveStableLabels (![1, 0, 1] : Fin 3 → ℕ) ![0, 1, 0]) =
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 := by
  rw [Tuple.sort_successiveStableLabels, sort_first, sort_second]

example : (fun i : Fin 3 =>
    (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) i) = ![1, 2, 0] := by
  decide

private theorem empty_left_block (β : Equiv.Perm (Fin 3)) :
    blockPermutation 0 3 1 β = β := by
  apply Equiv.ext
  intro i
  simpa using blockPermutation_natAdd 0 3 1 β i

example : (sortedBlockShuffle 0 3 (Equiv.swap (0 : Fin 3) 2)).perm = 1 := by
  have hl : blockRankLeft 0 3 (Equiv.swap (0 : Fin 3) 2) = 1 :=
    Subsingleton.elim _ _
  have hr : blockRankRight 0 3 (Equiv.swap (0 : Fin 3) 2) =
      Equiv.swap (0 : Fin 3) 2 := by
    unfold blockRankRight
    have h : (fun i : Fin 3 => Equiv.swap (0 : Fin 3) 2 (Fin.natAdd 0 i)) =
        Equiv.swap (0 : Fin 3) 2 := by
      funext i
      congr 1
      apply Fin.ext
      simp
    rw [h, Tuple.sort_perm]
    rfl
  change Equiv.swap (0 : Fin 3) 2 *
    blockPermutation 0 3 (blockRankLeft 0 3 _).symm (blockRankRight 0 3 _).symm = 1
  rw [hl, hr]
  simpa [empty_left_block] using mul_inv_cancel (Equiv.swap (0 : Fin 3) 2)

example : (sortedBlockShuffle 0 0 (1 : Equiv.Perm (Fin 0))).perm = 1 := by
  exact Subsingleton.elim _ _

end StableShuffleBoundaryTests
