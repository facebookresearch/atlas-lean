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

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Rank
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 6, Logic 7, Logic 22, Logic 38
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal Ordinal Set Order

-- Logic 6: Tree
def IsTree.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  ∀ x : α, IsChain (· ≤ ·) {y : α | y < x}

def level.{u} (α : Type u) [PartialOrder α] [WellFoundedLT α] (a : Ordinal.{u}) : Set α :=
  {x : α | WellFounded.rank (· < ·) x = a}


theorem level_lt_of_lt.{u} {α : Type u} [PartialOrder α] [WellFoundedLT α]
    {a b : Ordinal.{u}} {x y : α}
    (hx : x ∈ level α a) (hy : y ∈ level α b) (hxy : x < y) : a < b := by
  rw [level, Set.mem_setOf_eq] at hx hy
  rw [← hx, ← hy]
  exact WellFounded.rank_lt_of_rel hxy


theorem level_disjoint.{u} {α : Type u} [PartialOrder α] [WellFoundedLT α]
    {a b : Ordinal.{u}} (hab : a ≠ b) : Disjoint (level α a) (level α b) := by
  rw [Set.disjoint_left]
  rintro x hxa hxb
  rw [level, Set.mem_setOf_eq] at hxa hxb
  exact hab (hxa.symm.trans hxb)

-- Logic 22: $\kappa$ tree

open Cardinal in

 def IsTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
    IsTree α ∧
    (∀ x : α, ∃ a < κ.ord, x ∈ level α a) ∧
    (∀ a < κ.ord, (level α a).Nonempty ∧ #(level α a) < κ)


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

def IsNormalTreeAt.{u} (κ : Cardinal.{u}) (α : Type u) [PartialOrder α] [WellFoundedLT α] : Prop :=
  IsTreeAt κ α ∧
  (∃ r : α, ∀ x : α, r ≤ x) ∧
  (∀ x : α, ∀ b : Ordinal.{u},
      WellFounded.rank (· < ·) x < b → b < κ.ord →
      ∃ y : α, x < y ∧ WellFounded.rank (· < ·) y = b) ∧
  (∀ x : α, ∃ y z : α, x < y ∧ x < z ∧ ¬ (y ≤ z) ∧ ¬ (z ≤ y))


theorem not_isNormalTreeAt_nat (κ : Cardinal.{0}) : ¬ IsNormalTreeAt κ ℕ := by
  rintro ⟨-, -, -, hsplit⟩
  obtain ⟨y, z, -, -, hyz, hzy⟩ := hsplit 0
  exact (le_total y z).elim hyz hzy

end
