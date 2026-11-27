/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PermutationWordleCounts

open MetaMathlibExt

-- At lengths zero and one, the identity is the only secret for every strategy.
example (S : (m : ℕ) → Equiv.Perm (Fin m)) :
    permWordleCoeff S 0 1 = 1 ∧ permWordleCoeff S 0 2 = 0 :=
  permWordleCoeff_one_and_two 0 S (by intros; omega)

example (S : (m : ℕ) → Equiv.Perm (Fin m)) :
    permWordleCoeff S 1 1 = 1 ∧ permWordleCoeff S 1 2 = 0 :=
  permWordleCoeff_one_and_two 1 S (by intros; omega)

-- The three pairs of incorrect positions and the full triple give four two-guess solves.
example : permWordleCoeff cyclicShiftStrategy 3 2 = 4 := by
  apply (permWordleCoeff_one_and_two 3 cyclicShiftStrategy _).2
  intro m hm hn
  have : m = 2 ∨ m = 3 := by omega
  rcases this with rfl | rfl <;> decide
