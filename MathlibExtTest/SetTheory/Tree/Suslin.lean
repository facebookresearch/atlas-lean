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

public import MathlibExt.SetTheory.Tree.Suslin
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

open Cardinal Ordinal Set Order

namespace MathlibExtTest.SetTheory.Tree.Suslin

open MetaMathlibExt

-- Logic 24: $\kappa$-Suslin tree

theorem IsSuslinTreeAt.isAronszajnTreeAt.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsSuslinTreeAt κ α) : IsAronszajnTreeAt κ α := h.1

theorem _root_.MetaMathlibExt.IsSuslinTreeAt.isTreeAt.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsSuslinTreeAt κ α) : IsTreeAt κ α := h.1.1

-- Logic 19: Suslin tree

/-- Check 1: both bounds sit at `ℵ₁` — chains and antichains alike. Fails if either
clause used a different cardinal or the nesting were wrong. -/

theorem IsSuslinTree.chain_and_antichain_lt.{u} {α : Type u} [PartialOrder α] [WellFoundedLT α]
    (h : IsSuslinTree α) :
    (∀ C : Set α, IsChain (· ≤ ·) C → #C < aleph 1) ∧
      (∀ A : Set α, IsAntichain (· ≤ ·) A → #A < aleph 1) :=
  ⟨h.1.2, h.2⟩

/-- Check 2: no uncountable linear order is Suslin — in a linear order the whole type is
a chain. This is the branch-of-length-`ω₁` non-example, and it breaks if the chain bound
is `#C = κ` instead of `#C < κ`. -/

theorem not_isSuslinTree_of_linearOrder.{u} (α : Type u) [LinearOrder α] [WellFoundedLT α]
    (hα : ¬ #(Set.univ : Set α) < aleph 1) : ¬ IsSuslinTree α :=
  fun h => hα (h.1.2 Set.univ (fun x _ y _ _ => le_total x y))

/-- Check 3 (tests the antichain clause specifically): in a linear order every
`IsAntichain (· ≤ ·)` set is a subsingleton, so the antichain condition really is
incomparability. Fails if the relation were compatibility or `<`. -/

theorem antichain_subsingleton_of_linearOrder.{u} {α : Type u} [LinearOrder α] {A : Set α}
    (hA : IsAntichain (· ≤ ·) A) : A.Subsingleton := by
  intro x hx y hy
  by_contra hne
  rcases le_total x y with h | h
  · exact absurd h (hA hx hy hne)
  · exact absurd h (hA hy hx (Ne.symm hne))

end MathlibExtTest.SetTheory.Tree.Suslin

end
