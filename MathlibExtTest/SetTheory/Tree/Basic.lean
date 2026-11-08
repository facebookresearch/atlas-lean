/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner, Nam Trang
-/
module

public import MathlibExt.SetTheory.Tree.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

open Cardinal Ordinal Set Order

namespace MathlibExtTest.SetTheory.Tree.Basic

open MetaMathlibExt

-- Logic 6: Tree

/- Sanity check: the square `Bool × Bool` is not a tree —
    its top `(true, true)` has two incomparable predecessors. -/

example : ¬ IsTree (Bool × Bool) := by
  intro h
  have hm1 : ((true, false) : Bool × Bool) ∈ {y : Bool × Bool | y < (true, true)} := by
    simp [Set.mem_setOf_eq, Prod.lt_iff]
  have hm2 : ((false, true) : Bool × Bool) ∈ {y : Bool × Bool | y < (true, true)} := by
    simp [Set.mem_setOf_eq, Prod.lt_iff]
  have hc := h (true, true) hm1 hm2 (by simp)
  simp [Prod.le_def] at hc
  exact absurd hc (by decide)

-- Logic 7: Level of a well-founded partial ordering

/-- Sanity check: `level` respects the order — if `x < y`, then `x`'s level is
    strictly below `y`'s. (Levels stratify the order.) -/

theorem level_lt_of_lt.{u} {α : Type u} [PartialOrder α] [WellFoundedLT α]
    {a b : Ordinal.{u}} {x y : α}
    (hx : x ∈ level α a) (hy : y ∈ level α b) (hxy : x < y) : a < b := by
  rw [level, Set.mem_setOf_eq] at hx hy
  rw [← hx, ← hy]
  exact WellFounded.rank_lt_of_rel hxy

/-- Secondary check: distinct levels are disjoint (`rank` is a function). -/

theorem level_disjoint.{u} {α : Type u} [PartialOrder α] [WellFoundedLT α]
    {a b : Ordinal.{u}} (hab : a ≠ b) : Disjoint (level α a) (level α b) := by
  rw [Set.disjoint_left]
  rintro x hxa hxb
  rw [level, Set.mem_setOf_eq] at hxa hxb
  exact hab (hxa.symm.trans hxb)

-- Logic 22: $\kappa$ tree

/-- **A `κ`-tree has height exactly `κ`.**  Clause 2 of `IsTreeAt` bounds the realized levels
above and the nonemptiness half of clause 3 bounds them below, so together they pin the set of
nonempty levels to `Set.Iio κ.ord` on the nose — not merely inside it.-/

theorem nonempty_level_eq_of_isTreeAt.{u} {κ : Cardinal.{u}} {α : Type u} [PartialOrder α]
    [WellFoundedLT α] (h : IsTreeAt κ α) :
    {a : Ordinal.{u} | (level α a).Nonempty} = Set.Iio κ.ord := by
  ext a
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨b, hb, hxb⟩ := h.2.1 x
    have hxa : WellFounded.rank (α := α) (· < ·) x = a := hx
    have hxb' : WellFounded.rank (α := α) (· < ·) x = b := hxb
    have hab : a = b := by rw [← hxa, hxb']
    rw [Set.mem_Iio, hab]
    exact hb
  · intro ha
    exact (h.2.2 a (Set.mem_Iio.mp ha)).1

-- Logic 38: Normal tree

/-- Sanity check: no linear order is a normal tree, for any `κ`.  `ℕ` satisfies
`IsTreeAt ℵ₀`, has a root, and is well-pruned, so the splitting clause is the sole
obstruction — and it is exactly what fails here. -/

theorem not_isNormalTreeAt_nat (κ : Cardinal.{0}) : ¬ IsNormalTreeAt κ ℕ := by
  rintro ⟨-, -, -, hsplit⟩
  obtain ⟨y, z, -, -, hyz, hzy⟩ := hsplit 0
  exact (le_total y z).elim hyz hzy

end MathlibExtTest.SetTheory.Tree.Basic

end
