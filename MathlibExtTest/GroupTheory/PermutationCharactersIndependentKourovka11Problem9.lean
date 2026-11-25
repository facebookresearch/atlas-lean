/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PermutationCharactersIndependentKourovka11Problem9
import Mathlib.GroupTheory.Index

open MathlibExt.GroupTheory.PermutationCharactersIndependentKourovka11Problem9Wanted

variable {G : Type*} [Group G]

-- The identity fixes all the cosets.
example (H : Subgroup G) : permChar H 1 = H.index := by
  simp [permChar, Subgroup.index]

-- Every element fixes the unique coset of the whole group.
example (g : G) : permChar (⊤ : Subgroup G) g = 1 := by
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  have h (c : G ⧸ (⊤ : Subgroup G)) : g • c = c := Subsingleton.elim _ _
  simp [permChar, h]

-- A nonidentity element fixes no coset of the trivial subgroup.
example (g : G) (hg : g ≠ 1) : permChar (⊥ : Subgroup G) g = 0 := by
  have h (c : G ⧸ (⊥ : Subgroup G)) : g • c ≠ c := by
    induction c using Quotient.inductionOn with
    | h x =>
      intro hfix
      have hmul : g * x = x := congrArg (QuotientGroup.quotientEquivSelf G) hfix
      exact hg (mul_eq_right.mp hmul)
  simp [permChar, h]
