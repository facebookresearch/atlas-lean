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

public import MathlibExt.SetTheory.Tree.Aronszajn
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

open Cardinal

namespace MathlibExtTest.SetTheory.Tree.Aronszajn

open MetaMathlibExt

-- Logic 23: $\kappa$-Aronszajn tree

theorem _root_.MetaMathlibExt.IsAronszajnTreeAt.isTreeAt.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsAronszajnTreeAt κ α) : IsTreeAt κ α := h.1

theorem IsAronszajnTreeAt.isTree.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsAronszajnTreeAt κ α) : IsTree α := h.1.1

/-- **The chain clause forces `1 < κ` as soon as there is a node**, since a singleton is a
chain.  Exactly parallel to `IsSuslinTreeAt.one_lt`, but obtained from the *chain* clause rather
than the antichain one — so it survives deleting the Suslin conjunct. -/

theorem _root_.MetaMathlibExt.IsAronszajnTreeAt.one_lt.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsAronszajnTreeAt κ α) (x : α) : 1 < κ := by
  have hC : IsChain (· ≤ ·) ({x} : Set α) :=
    Set.Subsingleton.pairwise Set.subsingleton_singleton _
  have hlt := h.2 {x} hC
  rwa [Cardinal.mk_singleton] at hlt

-- Logic 12: Aronszajn tree

/-- Check 1: no uncountable linear order is Aronszajn — in a linear order the whole
type is a chain. This is the canonical non-example (a branch of length `ω₁`), and it
is exactly what breaks if the chain bound is `#C = κ` rather than `#C < κ`. -/

theorem not_isAronszajnTree_of_linearOrder.{u} (α : Type u) [LinearOrder α] [WellFoundedLT α]
    (hα : ¬ #(Set.univ : Set α) < aleph 1) : ¬ IsAronszajnTree α :=
  fun h => hα (h.2 Set.univ (fun x _ y _ _ => le_total x y))

/-- Check 2: levels partition by rank — a node lies in at most one level. Fails if
`level` were defined with `≤ a` instead of `= a`. -/

theorem level_eq_of_mem.{u} {α : Type u} [PartialOrder α] [WellFoundedLT α]
    {a b : Ordinal.{u}} {x : α} (ha : x ∈ level α a) (hb : x ∈ level α b) : a = b :=
  ha.symm.trans hb

/-- Check 3: an Aronszajn tree has no two nodes of the same rank in different levels,
and its height witness is unique — so `IsTreeAt`'s second clause determines a node's
level. -/

theorem level_unique.{u} {α : Type u} [PartialOrder α] [WellFoundedLT α]
    (h : IsAronszajnTree α) (x : α) :
    ∃! a : Ordinal.{u}, a < (aleph 1).ord ∧ x ∈ level α a := by
  obtain ⟨a, ha, hxa⟩ := h.1.2.1 x
  exact ⟨a, ⟨ha, hxa⟩, fun b hb => (level_eq_of_mem hb.2 hxa)⟩

-- Logic 8: ω₁-tree

open Cardinal in
  /- Sanity check: `ℕ` is not an ω₁-tree.  It is a well-founded linear order, so it
satisfies the tree and height-bound clauses,  level at `ω`
is empty.  This check is provable exactly because `IsTreeAt` demands that *every*
level below `κ.ord` be nonempty — i.e. heightt most `κ`. -/

example : ¬ IsOmega1Tree ℕ := by
  rintro ⟨-, -, hlev⟩
  have homega : Ordinal.omega0 < (aleph 1).ord := by
    rw [← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.2 Cardinal.aleph0_lt_aleph_one
  obtain ⟨⟨x, hx⟩, -⟩ := hlev _ homega
  rw [level, Set.mem_setOf_eq, WellFounded.rank_eq_typein] at hx
  have hx' : (x : Ordinal) = Ordinal.omega0 := (Ordinal.typein_lt_nat x).symm.trans hx
  exact absurd hx' (Ordinal.natCast_lt_omega0 x).ne

end MathlibExtTest.SetTheory.Tree.Aronszajn

end
