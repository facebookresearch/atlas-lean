/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Perm.ShuffleDescents
import MathlibExt.Combinatorics.Perm.CyclicDescentNumber
import Mathlib.Tactic.FinCases

/-!
# Ordinary and cyclic descents of three-letter permutations

Reversal has two adjacent descents. Identity has only the closing cyclic descent on three
letters, while the one-letter closing comparison contributes zero.
-/

noncomputable section

namespace PermutationDescentBoundaryTests

open Equiv.Perm

example : descentPositions (Equiv.swap (0 : Fin 3) 2) = {0, 1} := by
  ext i
  fin_cases i <;> simp [descentPositions, Equiv.swap_apply_def]

example : descentNumber (Equiv.swap (0 : Fin 3) 2) = 2 := by
  have h : descentPositions (Equiv.swap (0 : Fin 3) 2) = {0, 1} := by
    ext i
    fin_cases i <;> simp [descentPositions, Equiv.swap_apply_def]
  simp [descentNumber, h]

example : descentNumber (1 : Equiv.Perm (Fin 0)) = 0 := by
  exact (descentNumber_eq_zero_iff _).2 rfl

example : cyclicDescentNumber (1 : Equiv.Perm (Fin 3)) = 1 := by
  unfold cyclicDescentNumber
  decide

example : cyclicDescentNumber (1 : Equiv.Perm (Fin 1)) = 0 := by
  unfold cyclicDescentNumber
  decide

example : cyclicDescentNumber (Equiv.swap (0 : Fin 3) 2) = 2 := by
  unfold cyclicDescentNumber
  decide

end PermutationDescentBoundaryTests
