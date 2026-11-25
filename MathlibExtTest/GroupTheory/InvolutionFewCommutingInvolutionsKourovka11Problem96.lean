/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.InvolutionFewCommutingInvolutionsKourovka11Problem96
import Mathlib.GroupTheory.Perm.Basic

open MathlibExt.GroupTheory.InvolutionFewCommutingInvolutionsKourovka11Problem96Wanted

-- An involution counts itself, and the identity is excluded.
example {G : Type*} [Group G] (t : G) (ht : orderOf t = 2) :
    t ∈ commutingInvolutions t ∧ (1 : G) ∉ commutingInvolutions t := by
  simp [commutingInvolutions, ht]

-- Disjoint transpositions commute, while transpositions sharing one point do not.
example :
    Equiv.swap (2 : Fin 4) 3 ∈ commutingInvolutions (Equiv.swap 0 1) ∧
    Equiv.swap (1 : Fin 4) 2 ∉ commutingInvolutions (Equiv.swap 0 1) := by
  change (_ ∧ _) ∧ ¬ (_ ∧ _)
  rw [orderOf_eq_prime_iff]
  exact ⟨⟨⟨by decide, by decide⟩, by decide⟩, fun ⟨_, hcomm⟩ ↦ absurd hcomm (by decide)⟩
