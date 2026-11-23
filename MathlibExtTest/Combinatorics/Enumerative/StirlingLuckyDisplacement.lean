/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingLuckyDisplacement

open MetaMathlibExt

-- The empty word shows why the positive-order hypothesis is necessary.
example : IsAdmissibleLuckySet 0 ∅ :=
  ⟨Fin.elim0, by simp [IsStirlingPermutation], by decide⟩

example : 1 ∈ ({1} : Finset ℕ) ∧ 2 ∉ ({1} : Finset ℕ) := by
  apply IsAdmissibleLuckySet.one_mem_and_two_mul_not_mem 1 (by decide)
  exact ⟨![1, 1], by unfold IsStirlingPermutation; decide, by decide⟩

-- In 221133, car 2 takes spot 3 before either car preferring 3 arrives.
example : stirlingLuckySet (n := 3) ![2, 2, 1, 1, 3, 3] = {1, 3} := by decide
