/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang, Steven Warner
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.Tree.Aronszajn
public import MathlibExt.SetTheory.Tree.Basic
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 24, Logic 19
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal Ordinal Set Order

-- Logic 24: $\kappa$-Suslin tree
def IsSuslinTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsAronszajnTreeAt κ α ∧ ∀ A : Set α, IsAntichain (· ≤ ·) A → #A < κ

theorem IsSuslinTreeAt.isAronszajnTreeAt.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsSuslinTreeAt κ α) : IsAronszajnTreeAt κ α := h.1

theorem IsSuslinTreeAt.isTreeAt.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsSuslinTreeAt κ α) : IsTreeAt κ α := h.1.1

-- Logic 19: Suslin tree
def IsSuslinTree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  IsSuslinTreeAt (aleph 1) α

theorem IsSuslinTree.chain_and_antichain_lt.{u} {α : Type u} [PartialOrder α] [WellFoundedLT α]
    (h : IsSuslinTree α) :
    (∀ C : Set α, IsChain (· ≤ ·) C → #C < aleph 1) ∧
      (∀ A : Set α, IsAntichain (· ≤ ·) A → #A < aleph 1) :=
  ⟨h.1.2, h.2⟩

theorem not_isSuslinTree_of_linearOrder.{u} (α : Type u) [LinearOrder α] [WellFoundedLT α]
    (hα : ¬ #(Set.univ : Set α) < aleph 1) : ¬ IsSuslinTree α :=
  fun h => hα (h.1.2 Set.univ (fun x _ y _ _ => le_total x y))

theorem antichain_subsingleton_of_linearOrder.{u} {α : Type u} [LinearOrder α] {A : Set α}
    (hA : IsAntichain (· ≤ ·) A) : A.Subsingleton := by
  intro x hx y hy
  by_contra hne
  rcases le_total x y with h | h
  · exact absurd h (hA hx hy hne)
  · exact absurd h (hA hy hx (Ne.symm hne))

end
