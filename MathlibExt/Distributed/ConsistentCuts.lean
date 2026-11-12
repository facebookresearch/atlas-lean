/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.SetNotation
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section


/-- A cut of a partially ordered set of events is downward
closed (a consistent cut / ideal): if an event is in the cut,
every event below it (happened-before) is in the cut. -/
def DownClosed {E : Type*} [Preorder E] (S : Set E) : Prop :=
  ∀ x ∈ S, ∀ y ≤ x, y ∈ S

/-- The union of two consistent cuts is consistent. -/
theorem DownClosed.union {E : Type*} [Preorder E] {S T : Set E}
    (hS : DownClosed S) (hT : DownClosed T) : DownClosed (S ∪ T) := by
  intro x hx y hy
  simp only [Set.mem_union] at hx ⊢
  rcases hx with h | h
  · exact Or.inl (hS x h y hy)
  · exact Or.inr (hT x h y hy)

/-- The intersection of two consistent cuts is consistent:
consistent cuts form a lattice under inclusion. -/
theorem DownClosed.inter {E : Type*} [Preorder E] {S T : Set E}
    (hS : DownClosed S) (hT : DownClosed T) : DownClosed (S ∩ T) := by
  intro x hx y hy
  simp only [Set.mem_inter_iff] at hx ⊢
  exact ⟨hS x hx.1 y hy, hT x hx.2 y hy⟩

/-- The empty cut and the full cut are consistent. -/
theorem DownClosed.empty {E : Type*} [Preorder E] :
    DownClosed (∅ : Set E) := by
  intro x hx y hy
  simp at hx

theorem DownClosed.univ {E : Type*} [Preorder E] :
    DownClosed (Set.univ : Set E) := by
  intro x _ y _
  exact Set.mem_univ y

/-- A principal down-set (all events below a single event, the
cut "just after `x` on its process plus its causal past") is
consistent and contains `x`: `Iic x` is the smallest consistent
cut containing `x`. -/
theorem DownClosed.Iic {E : Type*} [Preorder E] (x : E) :
    DownClosed (Set.Iic x) := by
  intro z hz y hy
  simp only [Set.mem_Iic] at hz ⊢
  exact le_trans hy hz

theorem mem_Iic_self {E : Type*} [Preorder E] (x : E) :
    x ∈ Set.Iic x := by
  exact Set.mem_Iic.mpr le_rfl

/-- Minimality of the principal cut: any consistent cut
containing `x` contains the whole principal cut of `x`. -/
theorem DownClosed.Iic_minimal {E : Type*} [Preorder E] {S : Set E}
    (hS : DownClosed S) {x : E} (hx : x ∈ S) : Set.Iic x ⊆ S := by
  intro z hz
  simp only [Set.mem_Iic] at hz
  exact hS x hx z hz
