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
public import MathlibExt.SetTheory.Tree.Basic
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 23, Logic 12, Logic 8
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal

-- Logic 23: $\kappa$-Aronszajn tree
open Cardinal in
def IsAronszajnTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsTreeAt κ α ∧ ∀ C : Set α, IsChain (· ≤ ·) C → #C < κ


theorem IsAronszajnTreeAt.isTreeAt.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsAronszajnTreeAt κ α) : IsTreeAt κ α := h.1


theorem IsAronszajnTreeAt.isTree.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsAronszajnTreeAt κ α) : IsTree α := h.1.1


theorem IsAronszajnTreeAt.one_lt.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsAronszajnTreeAt κ α) (x : α) : 1 < κ := by
  have hC : IsChain (· ≤ ·) ({x} : Set α) :=
    Set.Subsingleton.pairwise Set.subsingleton_singleton _
  have hlt := h.2 {x} hC
  rwa [Cardinal.mk_singleton] at hlt

-- Logic 12: Aronszajn tree

open Cardinal in

def IsAronszajnTree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsAronszajnTreeAt (aleph 1) α


theorem not_isAronszajnTree_of_linearOrder.{u} (α : Type u) [LinearOrder α] [WellFoundedLT α]
    (hα : ¬ #(Set.univ : Set α) < aleph 1) : ¬ IsAronszajnTree α :=
  fun h => hα (h.2 Set.univ (fun x _ y _ _ => le_total x y))


theorem level_eq_of_mem.{u} {α : Type u} [PartialOrder α] [WellFoundedLT α]
    {a b : Ordinal.{u}} {x : α} (ha : x ∈ level α a) (hb : x ∈ level α b) : a = b :=
  ha.symm.trans hb


theorem level_unique.{u} {α : Type u} [PartialOrder α] [WellFoundedLT α]
    (h : IsAronszajnTree α) (x : α) :
    ∃! a : Ordinal.{u}, a < (aleph 1).ord ∧ x ∈ level α a := by
  obtain ⟨a, ha, hxa⟩ := h.1.2.1 x
  exact ⟨a, ⟨ha, hxa⟩, fun b hb => (level_eq_of_mem hb.2 hxa)⟩

-- Logic 8: ω₁-tree

open Cardinal in

def IsOmega1Tree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  IsTreeAt (aleph 1 : Cardinal.{u}) α

end
