/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SylverCoinageEnder
import Mathlib.NumberTheory.FrobeniusNumber

open MetaMathlibExt

-- The gaps of {3, 4} are 1, 2 and 5. Either smaller gap generates 5 when played.
example : IsSylverNPosition {3, 4} := by
  have hF : IsGreatest (sylverLegalMoves {3, 4}) 5 :=
    frobeniusNumber_pair (m := 3) (n := 4) (by decide) (by decide) (by decide)
  refine isSylverNPosition_of_ender (hF := hF) (hender := ?_) (hF1 := by decide)
  intro x hx
  by_contra hne
  have hxle := hF.2 hx.1
  have hx0 : x ≠ 0 := fun heq => zero_notMem_sylverLegalMoves _ (heq ▸ hx.1)
  have hxnot : x ∉ ({3, 4} : Set ℕ) := fun h => hx.1 (AddSubmonoid.subset_closure h)
  have hcomp : 5 - x ∈ ({3, 4} : Set ℕ) := by
    simp at hxnot ⊢
    omega
  apply hx.2 5 hF.1 (Ne.symm hne)
  have hsum := add_mem (AddSubmonoid.subset_closure (Set.mem_insert x ({3, 4} : Set ℕ)))
    (AddSubmonoid.subset_closure (Set.mem_insert_of_mem x hcomp))
  simpa only [Nat.add_sub_of_le hxle] using hsum
