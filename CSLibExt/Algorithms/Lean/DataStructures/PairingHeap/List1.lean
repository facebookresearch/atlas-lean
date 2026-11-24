/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap.PriorityQueue
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic

/-!
# Pairing heaps: Okasaki's list version (`Pairing_Heap_List1`)

The second of the three pairing-heap variants in the AFP. Unlike the
book version (`List2`), `merge` is direct (not via `link`), `pass2` is
a left fold with `merge`, and `mergePairs` merges adjacent pairs
directly. Correctness does not require the heap invariant for the
operations themselves (`pheap` plays the role of `invar`).

Includes the functional-correctness proof and the
`Priority_Queue_Merge` specification in the locale's and the book's
forms. The List1 amortized analyses (the direct `sum_ub` route, the
tree-potential route, and the transfer from the Tree analysis) are
not ported; `PairingHeap.Amortized` contains only the `List2` and
`Tree` analyses.

`getMin` is `Option`-valued: the book's `get_min` is partial on the
empty heap.

Ported from the Chapter 23 Lean conversion in
`converted_proofs/ch23/lean/Chapter23.lean`, itself a conversion of the
Isabelle/HOL sources: the AFP entries `Pairing_Heap`
(`Pairing_Heap_List1.thy`) and `Amortized_Complexity`
(`Pairing_Heap_List1_Analysis*.thy`), and Tobias Nipkow (ed.),
*Functional Data Structures and Algorithms: A Proof Assistant Approach*,
Chapter 23 (Pairing Heaps, pp. 257–264). Isabelle-derived names are kept
for traceability to those sources.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace PairingHeap
namespace List1

variable {α : Type u}

/-- The List1 heap type: `datatype 'a heap = Empty | Hp 'a ('a heap list)`.
A nested inductive (like `List2.Hp`), so the size / multiset /
heap-property functions recurse through `List.map` / `∀`, and induction
uses the hand-rolled `Heap_ind` below. -/
inductive Heap (α : Type u) where
  | empty : Heap α
  | hp : α → List (Heap α) → Heap α

/-- The size of a List1 heap (number of `hp` nodes). -/
def sizeHeap : Heap α → ℕ
  | .empty => 0
  | .hp _ hs => 1 + (hs.map sizeHeap).sum

theorem sizeHeap_empty : sizeHeap (Heap.empty : Heap α) = 0 := by simp [sizeHeap]

theorem sizeHeap_hp (x : α) (hs : List (Heap α)) :
    sizeHeap (.hp x hs) = 1 + (hs.map sizeHeap).sum := by simp [sizeHeap]

theorem sizeHeap_le_sum_of_mem {hs : List (Heap α)} {h : Heap α}
    (hh : h ∈ hs) : sizeHeap h ≤ (hs.map sizeHeap).sum := by
  induction hs with
  | nil => simp at hh
  | cons h' hs ih =>
    simp only [List.mem_cons] at hh
    simp only [List.map_cons, List.sum_cons]
    rcases hh with rfl | hh
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih hh) (Nat.le_add_left _ _)

theorem sizeHeap_lt_of_mem {hs : List (Heap α)} {h : Heap α} (x : α)
    (hh : h ∈ hs) : sizeHeap h < sizeHeap (.hp x hs) := by
  have hle := sizeHeap_le_sum_of_mem hh
  rw [sizeHeap_hp]
  omega

/-- Strong induction on List1 heaps, by `sizeHeap` (same shape as
`List2.Hp_ind`; Lean's `induction` does not support nested inductives). -/
theorem Heap_ind {P : Heap α → Prop}
    (empty : P .empty)
    (step : ∀ (x : α) (hs : List (Heap α)), (∀ h ∈ hs, P h) → P (.hp x hs))
    (h : Heap α) : P h := by
  have key : ∀ n : ℕ, ∀ h : Heap α, sizeHeap h ≤ n → P h := by
    intro n
    induction n with
    | zero =>
      intro h hh
      cases h with
      | empty => exact empty
      | hp x hs =>
        rw [sizeHeap_hp] at hh
        omega
    | succ n ih =>
      intro h hh
      cases h with
      | empty => exact empty
      | hp x hs =>
        apply step
        intro h' hh'
        apply ih
        have hlt := sizeHeap_lt_of_mem x hh'
        have hsz := sizeHeap_hp x hs
        omega
  exact key (sizeHeap h) h le_rfl

/-- AFP `mset_heap`. -/
def msetHeap : Heap α → Multiset α
  | .empty => 0
  | .hp x hs => {x} + (hs.map msetHeap).sum

theorem msetHeap_empty : msetHeap (Heap.empty : Heap α) = 0 := by simp [msetHeap]

theorem msetHeap_hp (x : α) (hs : List (Heap α)) :
    msetHeap (.hp x hs) = {x} + (hs.map msetHeap).sum := by simp [msetHeap]

/-- AFP `pheap` (on the heap type; `empty` maps to `True`). -/
def pheap [LinearOrder α] : Heap α → Prop
  | .empty => True
  | .hp x hs => ∀ h ∈ hs, (∀ y ∈ msetHeap h, x ≤ y) ∧ pheap h

theorem pheap_empty [LinearOrder α] : pheap (Heap.empty : Heap α) ↔ True := by
  simp [pheap]

theorem pheap_hp [LinearOrder α] (x : α) (hs : List (Heap α)) :
    pheap (.hp x hs) ↔ ∀ h ∈ hs, (∀ y ∈ msetHeap h, x ≤ y) ∧ pheap h := by
  simp [pheap]

/-- Membership in a summed list of multisets comes from one of the heaps. -/
theorem mem_msetHeap_map {hs : List (Heap α)} {z : α}
    (hz : z ∈ (hs.map msetHeap).sum) : ∃ h ∈ hs, z ∈ msetHeap h := by
  induction hs with
  | nil => simp at hz
  | cons h hs ih =>
    simp only [List.map_cons, List.sum_cons, Multiset.mem_add] at hz
    rcases hz with hz | hz
    · exact ⟨h, List.mem_cons_self, hz⟩
    · obtain ⟨h', hh', hz'⟩ := ih hz
      exact ⟨h', List.mem_cons_of_mem _ hh', hz'⟩

/-- `get_min` (List1 version): partial on `empty`, totalized to `Option`. -/
def getMin : Heap α → Option α
  | .empty => none
  | .hp x _ => some x

theorem getMin_empty : getMin (Heap.empty : Heap α) = none := rfl

theorem getMin_hp (x : α) (hs : List (Heap α)) :
    getMin (.hp x hs) = some x := rfl

/-- `merge` (List1 version): direct, not via `link`. -/
def merge [LinearOrder α] : Heap α → Heap α → Heap α
  | .empty, h => h
  | h, .empty => h
  | .hp x hsx, .hp y hsy =>
    if x < y then .hp x (.hp y hsy :: hsx) else .hp y (.hp x hsx :: hsy)

theorem merge_empty_left [LinearOrder α] (h : Heap α) : merge .empty h = h := rfl

theorem merge_empty_right [LinearOrder α] (h : Heap α) : merge h .empty = h := by
  cases h <;> rfl

theorem merge_hp_hp_pos [LinearOrder α] {x y : α} {hsx hsy : List (Heap α)}
    (h : x < y) :
    merge (.hp x hsx) (.hp y hsy) = .hp x (.hp y hsy :: hsx) := by
  simp [merge, h]

theorem merge_hp_hp_neg [LinearOrder α] {x y : α} {hsx hsy : List (Heap α)}
    (h : ¬ x < y) :
    merge (.hp x hsx) (.hp y hsy) = .hp y (.hp x hsx :: hsy) := by
  simp [merge, h]

/-- `insert` (List1 version). -/
def insert [LinearOrder α] (x : α) (h : Heap α) : Heap α := merge (.hp x []) h

theorem insert_eq [LinearOrder α] (x : α) (h : Heap α) :
    insert x h = merge (.hp x []) h := rfl

/-- `pass1` (List1 version). -/
def pass1 [LinearOrder α] : List (Heap α) → List (Heap α)
  | h1 :: h2 :: hs => merge h1 h2 :: pass1 hs
  | hs => hs

theorem pass1_nil [LinearOrder α] : pass1 ([] : List (Heap α)) = [] := rfl

theorem pass1_single [LinearOrder α] (h : Heap α) : pass1 [h] = [h] := rfl

theorem pass1_cons2 [LinearOrder α] (h1 h2 : Heap α) (hs : List (Heap α)) :
    pass1 (h1 :: h2 :: hs) = merge h1 h2 :: pass1 hs := rfl

/-- `pass2` (List1 version): a left fold with `merge`. -/
def pass2 [LinearOrder α] : List (Heap α) → Heap α
  | [] => .empty
  | h :: hs => merge h (pass2 hs)

theorem pass2_nil [LinearOrder α] : pass2 ([] : List (Heap α)) = .empty := rfl

theorem pass2_cons [LinearOrder α] (h : Heap α) (hs : List (Heap α)) :
    pass2 (h :: hs) = merge h (pass2 hs) := rfl

/-- `merge_pairs` (List1 version). -/
def mergePairs [LinearOrder α] : List (Heap α) → Heap α
  | [] => .empty
  | [h] => h
  | h1 :: h2 :: hs => merge (merge h1 h2) (mergePairs hs)

theorem mergePairs_nil [LinearOrder α] :
    mergePairs ([] : List (Heap α)) = .empty := rfl

theorem mergePairs_single [LinearOrder α] (h : Heap α) : mergePairs [h] = h := rfl

theorem mergePairs_cons2 [LinearOrder α] (h1 h2 : Heap α) (hs : List (Heap α)) :
    mergePairs (h1 :: h2 :: hs) = merge (merge h1 h2) (mergePairs hs) := rfl

/-- `del_min` (List1 version). -/
def delMin [LinearOrder α] : Heap α → Heap α
  | .empty => .empty
  | .hp _ hs => pass2 (pass1 hs)

theorem delMin_empty [LinearOrder α] : delMin (Heap.empty : Heap α) = .empty := rfl

theorem delMin_hp [LinearOrder α] (x : α) (hs : List (Heap α)) :
    delMin (.hp x hs) = pass2 (pass1 hs) := rfl

/-- AFP `pass12_merge_pairs`: `pass2 (pass1 hs) = merge_pairs hs`. -/
theorem pass12_mergePairs [LinearOrder α] (hs : List (Heap α)) :
    pass2 (pass1 hs) = mergePairs hs := by
  induction hs using List_pair_ind with
  | nil => rfl
  | single h =>
    rw [pass1_single, pass2_cons, pass2_nil, merge_empty_right,
      mergePairs_single]
  | cons2 h1 h2 hs ih =>
    rw [pass1_cons2, pass2_cons, ih, mergePairs_cons2]

/-- AFP `mset_heap_empty_iff`. -/
theorem msetHeap_empty_iff (h : Heap α) : msetHeap h = 0 ↔ h = .empty := by
  cases h with
  | empty => simp [msetHeap_empty]
  | hp x hs =>
    constructor
    · intro hcontra
      have hc := congrArg Multiset.card hcontra
      simp only [msetHeap_hp, Multiset.card_add, Multiset.card_singleton,
        Multiset.card_zero] at hc
      omega
    · intro hcontra
      simp at hcontra

/-- AFP `pheap_merge`. -/
theorem pheap_merge [LinearOrder α] {h1 h2 : Heap α} (hp1 : pheap h1)
    (hp2 : pheap h2) : pheap (merge h1 h2) := by
  cases h1 with
  | empty => rw [merge_empty_left]; exact hp2
  | hp x hsx =>
    cases h2 with
    | empty => rw [merge_empty_right]; exact hp1
    | hp y hsy =>
      have hp1' := (pheap_hp x hsx).mp hp1
      have hp2' := (pheap_hp y hsy).mp hp2
      by_cases hc : x < y
      · rw [merge_hp_hp_pos hc, pheap_hp]
        intro h hh
        simp only [List.mem_cons] at hh
        rcases hh with rfl | hh
        · refine ⟨?_, hp2⟩
          intro z hz
          rw [msetHeap_hp] at hz
          rw [Multiset.mem_add] at hz
          rcases hz with hz | hz
          · rw [Multiset.mem_singleton] at hz
            subst hz
            exact le_of_lt hc
          · obtain ⟨h', hh', hzm⟩ := mem_msetHeap_map hz
            have hyz := (hp2' h' hh').1 z hzm
            exact le_trans (le_of_lt hc) hyz
        · exact hp1' h hh
      · rw [merge_hp_hp_neg hc, pheap_hp]
        intro h hh
        simp only [List.mem_cons] at hh
        rcases hh with rfl | hh
        · refine ⟨?_, hp1⟩
          intro z hz
          rw [msetHeap_hp] at hz
          rw [Multiset.mem_add] at hz
          rcases hz with hz | hz
          · rw [Multiset.mem_singleton] at hz
            subst hz
            exact le_of_not_gt hc
          · obtain ⟨h', hh', hzm⟩ := mem_msetHeap_map hz
            have hxz := (hp1' h' hh').1 z hzm
            exact le_trans (le_of_not_gt hc) hxz
        · exact hp2' h hh

/-- AFP `pheap_merge_pairs`. -/
theorem pheap_mergePairs [LinearOrder α] {hs : List (Heap α)}
    (hall : ∀ h ∈ hs, pheap h) : pheap (mergePairs hs) := by
  induction hs using List_pair_ind with
  | nil => simp [mergePairs, pheap]
  | single h =>
    rw [mergePairs_single]
    exact hall h List.mem_cons_self
  | cons2 h1 h2 hs ih =>
    rw [mergePairs_cons2]
    apply pheap_merge _ (ih (fun h hh =>
      hall h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh))))
    apply pheap_merge
    · exact hall h1 (by simp)
    · exact hall h2 (by simp)

/-- AFP `pheap_insert`. -/
theorem pheap_insert [LinearOrder α] {x : α} {h : Heap α} (hp : pheap h) :
    pheap (insert x h) := by
  rw [insert_eq]
  apply pheap_merge _ hp
  simp [pheap]

/-- AFP `pheap_del_min` (via `pass12_merge_pairs` and
`pheap_merge_pairs`, as in the AFP). -/
theorem pheap_delMin [LinearOrder α] {h : Heap α} (hp : pheap h) :
    pheap (delMin h) := by
  cases h with
  | empty => simp [delMin, pheap]
  | hp x hs =>
    rw [delMin_hp, pass12_mergePairs]
    apply pheap_mergePairs
    intro h hh
    have hp' := (pheap_hp x hs).mp hp
    exact (hp' h hh).2

/-- AFP `mset_merge`. -/
theorem mset_merge [LinearOrder α] (h1 h2 : Heap α) :
    msetHeap (merge h1 h2) = msetHeap h1 + msetHeap h2 := by
  cases h1 with
  | empty => simp [merge, msetHeap]
  | hp x hsx =>
    cases h2 with
    | empty => simp [merge, msetHeap]
    | hp y hsy =>
      by_cases hc : x < y
      · rw [merge_hp_hp_pos hc]
        simp only [msetHeap_hp, List.map_cons, List.sum_cons]
        ac_rfl
      · rw [merge_hp_hp_neg hc]
        simp only [msetHeap_hp, List.map_cons, List.sum_cons]
        ac_rfl

/-- AFP `mset_insert`. -/
theorem mset_insert [LinearOrder α] (a : α) (h : Heap α) :
    msetHeap (insert a h) = {a} + msetHeap h := by
  rw [insert_eq, mset_merge]
  simp [msetHeap]

/-- AFP `mset_merge_pairs`: the multiset of `merge_pairs hs` is the sum
of the multisets of the heaps in `hs`. -/
theorem mset_mergePairs [LinearOrder α] (hs : List (Heap α)) :
    msetHeap (mergePairs hs) = (hs.map msetHeap).sum := by
  induction hs using List_pair_ind with
  | nil => simp [mergePairs, msetHeap]
  | single h => simp [mergePairs]
  | cons2 h1 h2 hs ih =>
    rw [mergePairs_cons2, mset_merge, mset_merge, ih]
    simp only [List.map_cons, List.sum_cons]
    ac_rfl

/-- AFP `get_min_in`. -/
theorem getMin_mem (h : Heap α) (x : α) (hx : getMin h = some x) :
    x ∈ msetHeap h := by
  cases h with
  | empty => simp [getMin] at hx
  | hp y hs =>
    simp only [getMin, Option.some.injEq] at hx
    subst hx
    simp [msetHeap]

/-- AFP `get_min_min`. -/
theorem getMin_le [LinearOrder α] (h : Heap α) (x y : α) (hx : getMin h = some x)
    (hp : pheap h) (hy : y ∈ msetHeap h) : x ≤ y := by
  cases h with
  | empty => simp [getMin] at hx
  | hp z hs =>
    simp only [getMin, Option.some.injEq] at hx
    subst hx
    have hp' := (pheap_hp z hs).mp hp
    rw [msetHeap_hp] at hy
    rw [Multiset.mem_add] at hy
    rcases hy with hy | hy
    · rw [Multiset.mem_singleton] at hy
      subst hy
      exact le_refl _
    · obtain ⟨h', hh', hzm⟩ := mem_msetHeap_map hy
      exact (hp' h' hh').1 y hzm

/-- The `IsLeast` form of the AFP's `get_min` lemma
(`get_min h = Min_mset (mset_heap h)`). -/
theorem getMin_isLeast [LinearOrder α] (h : Heap α) (x : α)
    (hx : getMin h = some x) (hp : pheap h) :
    IsLeast {y | y ∈ msetHeap h} x := by
  refine ⟨getMin_mem h x hx, ?_⟩
  intro y hy
  exact getMin_le h x y hx hp hy

/-- `getMin` is defined on every nonempty heap: the definedness clause
of the `Priority_Queue_Merge` specifications. -/
theorem getMin_defined (h : Heap α) (hne : msetHeap h ≠ 0) :
    ∃ x, getMin h = some x := by
  cases h with
  | empty => simp [msetHeap] at hne
  | hp x hs => exact ⟨x, rfl⟩

/-- AFP `mset_del_min`. -/
theorem mset_delMin [LinearOrder α] {h : Heap α} {x : α}
    (hx : getMin h = some x) :
    msetHeap (delMin h) = msetHeap h - {x} := by
  cases h with
  | empty => simp [getMin] at hx
  | hp y hs =>
    simp only [getMin, Option.some.injEq] at hx
    subst hx
    rw [delMin_hp, pass12_mergePairs, mset_mergePairs, msetHeap_hp,
      Multiset.singleton_add, Multiset.sub_singleton, Multiset.erase_cons_head]

/-- `is_empty` of the `Priority_Queue` locale for the List1 variant:
`λh. h = empty` in the AFP interpretation. -/
def isEmpty : Heap α → Prop := fun h => h = .empty

/-- The `Priority_Queue_Merge` specification for the List1 variant, in the
Isabelle locale's form (`pairing: Priority_Queue_Merge` in
`Pairing_Heap_List1.thy`), with `invar = pheap` and `mset = mset_heap`,
plus the definedness clause. -/
theorem priority_queue_merge_locale [LinearOrder α] :
    PriorityQueueMergeSpec (Heap.empty : Heap α) isEmpty merge insert delMin getMin
      pheap msetHeap := by
  unfold PriorityQueueMergeSpec
  refine ⟨msetHeap_empty, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h _
    exact (msetHeap_empty_iff h).symm
  · intro x h hp
    rw [mset_insert x h]
    exact add_comm _ _
  · intro h x hp _ hx
    exact mset_delMin hx
  · intro h x hp _ hx
    exact getMin_isLeast h x hx hp
  · intro h hne
    exact getMin_defined h hne
  · simp [pheap]
  · intro x h hp
    exact pheap_insert hp
  · intro h hp _
    exact pheap_delMin hp
  · intro h1 h2 hp1 hp2
    exact mset_merge h1 h2
  · intro h1 h2 hp1 hp2
    exact pheap_merge hp1 hp2

/-- The `Priority_Queue_Merge` specification for the List1 variant in the
book's form (Chapter 14, Figures 14.1–14.2): the book's 9 properties,
no `is_empty`, plus the definedness clause. -/
theorem priority_queue_merge_book [LinearOrder α] :
    PriorityQueueSpec (Heap.empty : Heap α) merge insert delMin getMin pheap
      msetHeap := by
  unfold PriorityQueueSpec
  refine ⟨msetHeap_empty, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pheap]
  · intro x h hp
    rw [mset_insert x h]
    exact add_comm _ _
  · intro x h hp
    exact pheap_insert hp
  · intro h x hp _ hx
    exact mset_delMin hx
  · intro h hp _
    exact pheap_delMin hp
  · intro h x hp _ hx
    exact getMin_isLeast h x hx hp
  · intro h hne
    exact getMin_defined h hne
  · intro h1 h2 hp1 hp2
    exact mset_merge h1 h2
  · intro h1 h2 hp1 hp2
    exact pheap_merge hp1 hp2

end List1

end PairingHeap

end Cslib.Algorithms.Lean
