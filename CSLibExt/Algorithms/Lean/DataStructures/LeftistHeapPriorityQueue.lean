/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LeftistHeap
public import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Tactic
@[expose] public section

universe u

namespace Cslib.Algorithms.Lean.LHeap

private theorem all_le_mem_le {α : Type u} [LE α] {x y : α} {t : LHeap α}
    (ha : all_le x t) (hm : y ∈ mset_tree t) : x ≤ y := by
  revert ha hm
  induction t with
  | E =>
    intro ha hm
    simp [mset_tree] at hm
  | N rk w l r ihl ihr =>
    intro ha hm
    simp only [all_le] at ha
    obtain ⟨hle, hal, har⟩ := ha
    simp only [mset_tree] at hm
    rcases Multiset.mem_add.mp hm with h' | hmr
    · rcases Multiset.mem_add.mp h' with hw | hml
      · have hyw : y = w := Multiset.mem_singleton.mp hw
        rw [hyw]
        exact hle
      · exact ihl hal hml
    · exact ihr har hmr

/-- Insert one element into a leftist heap (merge with a singleton). -/
def insert {α : Type u} [LinearOrder α] (h : LHeap α) (x : α) : LHeap α :=
  merge (singleton x) h

/-- Root element of a leftist heap, if any. Under the `heap` invariant the
root is a minimum of the heap's elements (see `findMin?_le`); without the
invariant this is only root inspection. -/
def findMin? {α : Type u} : LHeap α → Option α
  | .E => none
  | .N _ x _ _ => some x

/-- Remove and return the root element, merging the two subtrees. Under the
`heap` invariant the returned element is a minimum of the original heap (see
`extractMin_le`); without the invariant this is only root removal. -/
def extractMin {α : Type u} [LinearOrder α] : LHeap α → Option (α × LHeap α)
  | .E => none
  | .N _ x l r => some (x, merge l r)

theorem findMin?_eq_none_iff {α : Type u} {h : LHeap α} : findMin? h = none ↔ h = .E := by
  cases h <;> simp [findMin?]

theorem insert_mset {α : Type u} [LinearOrder α] (h : LHeap α) (x : α) :
    mset_tree (insert h x) = {x} + mset_tree h := by
  simp only [insert, mset_merge, mset_singleton]

theorem heap_insert {α : Type u} [LinearOrder α] {h : LHeap α} (hh : heap h) (x : α) :
    heap (insert h x) := by
  simp only [insert]
  exact heap_merge _ _ (heap_singleton x) hh

theorem ltree_insert {α : Type u} [LinearOrder α] {h : LHeap α} (hl : ltree h) (x : α) :
    ltree (insert h x) := by
  simp only [insert]
  exact ltree_merge _ _ (ltree_singleton x) hl

theorem findMin?_mem {α : Type u} {h : LHeap α} {x : α} (hx : findMin? h = some x) :
    x ∈ mset_tree h := by
  cases h with
  | E => simp [findMin?] at hx
  | N rk y l r =>
    simp only [findMin?, Option.some.injEq] at hx
    subst hx
    simp [mset_tree]

theorem findMin?_le {α : Type u} [LinearOrder α] {h : LHeap α} {x y : α} (hh : heap h)
    (hx : findMin? h = some x) (hy : y ∈ mset_tree h) : x ≤ y := by
  cases h with
  | E => simp [findMin?] at hx
  | N rk z l r =>
    simp only [findMin?, Option.some.injEq] at hx
    rw [← hx]
    simp only [heap] at hh
    obtain ⟨hal, har, -, -⟩ := hh
    simp only [mset_tree] at hy
    rcases Multiset.mem_add.mp hy with h' | hmr
    · rcases Multiset.mem_add.mp h' with hw | hml
      · have hyz : y = z := Multiset.mem_singleton.mp hw
        subst hyz
        simp
      · exact all_le_mem_le hal hml
    · exact all_le_mem_le har hmr

theorem extractMin_eq_none_iff {α : Type u} [LinearOrder α] {h : LHeap α} :
    extractMin h = none ↔ h = .E := by
  cases h <;> simp [extractMin]

theorem extractMin_mset {α : Type u} [LinearOrder α] {h h' : LHeap α} {x : α}
    (hx : extractMin h = some (x, h')) : {x} + mset_tree h' = mset_tree h := by
  cases h with
  | E => simp [extractMin] at hx
  | N rk z l r =>
    simp only [extractMin, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    simp [mset_tree, mset_merge]

theorem extractMin_le {α : Type u} [LinearOrder α] {h h' : LHeap α} {x y : α} (hh : heap h)
    (hx : extractMin h = some (x, h')) (hy : y ∈ mset_tree h) : x ≤ y := by
  cases h with
  | E => simp [extractMin] at hx
  | N rk z l r =>
    simp only [extractMin, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    simp only [heap] at hh
    obtain ⟨hal, har, -, -⟩ := hh
    simp only [mset_tree] at hy
    rcases Multiset.mem_add.mp hy with h' | hmr
    · rcases Multiset.mem_add.mp h' with hw | hml
      · have hyz : y = z := Multiset.mem_singleton.mp hw
        subst hyz
        simp
      · exact all_le_mem_le hal hml
    · exact all_le_mem_le har hmr

theorem heap_extractMin {α : Type u} [LinearOrder α] {h h' : LHeap α} {x : α} (hh : heap h)
    (hx : extractMin h = some (x, h')) : heap h' := by
  cases h with
  | E => simp [extractMin] at hx
  | N rk z l r =>
    simp only [extractMin, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    simp only [heap] at hh
    obtain ⟨-, -, hhl, hhr⟩ := hh
    exact heap_merge _ _ hhl hhr

theorem ltree_extractMin {α : Type u} [LinearOrder α] {h h' : LHeap α} {x : α} (hl : ltree h)
    (hx : extractMin h = some (x, h')) : ltree h' := by
  cases h with
  | E => simp [extractMin] at hx
  | N rk z l r =>
    simp only [extractMin, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    simp only [ltree] at hl
    obtain ⟨-, -, hll, hlr⟩ := hl
    exact ltree_merge _ _ hll hlr

end Cslib.Algorithms.Lean.LHeap
