/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap

/-!
# Pairing-heap public proof-interface tests

Clients of the pairing-heap API can use the three variants' correctness
lemmas, the full `Priority_Queue_Merge` specification statements (in the
locale's, the book's, and — for `List2` — the strengthened form), and
Exercise 23.1 — not merely selected projections. No amortized claim is
inferred from the `T_*` bounds here; those live in
`PairingHeap.Amortized`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.PairingHeapAPITests

open PairingHeap

variable {α : Type u} [LinearOrder α]

-- The shared two-step list induction principle is available.
example {P : List α → Prop} (h0 : P []) (h1 : ∀ a : α, P [a])
    (h2 : ∀ a b : α, ∀ hs : List α, P hs → P (a :: b :: hs)) (hs : List α) :
    P hs :=
  List_pair_ind h0 h1 h2 hs

-- Check the complete `List2` correctness statements.
example {ho1 ho2 : List2.Heap α} :
    List2.msetHeap (List2.merge ho1 ho2) =
      List2.msetHeap ho1 + List2.msetHeap ho2 :=
  List2.mset_merge ho1 ho2

example {x : α} {ho : List2.Heap α} (h : List2.invar ho) :
    List2.invar (List2.insert x ho) :=
  List2.invar_insert h

example {ho : List2.Heap α} (h : List2.invar ho) :
    List2.invar (List2.delMin ho) :=
  List2.invar_delMin h

example {ho : List2.Heap α} {x y : α} (hx : List2.getMin ho = some x)
    (hinv : List2.invar ho) (hy : y ∈ List2.msetHeap ho) : x ≤ y :=
  List2.getMin_le ho x y hx hinv hy

-- Check the complete `List2` specification: the strengthened form.
example :
    (List2.msetHeap (List2.empty : List2.Heap α) = 0) ∧
    (∀ ho : List2.Heap α, List2.msetHeap ho = 0 ↔ ho = none) ∧
    (∀ (x : α) (ho : List2.Heap α),
      List2.msetHeap (List2.insert x ho) = {x} + List2.msetHeap ho) ∧
    (∀ (ho : List2.Heap α) (x : α), List2.getMin ho = some x →
      List2.msetHeap (List2.delMin ho) = List2.msetHeap ho - {x}) ∧
    (∀ (ho : List2.Heap α) (x : α), List2.getMin ho = some x →
      x ∈ List2.msetHeap ho) ∧
    (∀ (ho : List2.Heap α) (x y : α), List2.getMin ho = some x →
      List2.invar ho → y ∈ List2.msetHeap ho → x ≤ y) ∧
    (∀ (ho : List2.Heap α), List2.msetHeap ho ≠ 0 →
      ∃ x, List2.getMin ho = some x) ∧
    List2.invar (List2.empty : List2.Heap α) ∧
    (∀ (x : α) (ho : List2.Heap α), List2.invar ho →
      List2.invar (List2.insert x ho)) ∧
    (∀ ho : List2.Heap α, List2.invar ho → List2.invar (List2.delMin ho)) ∧
    (∀ (ho1 ho2 : List2.Heap α),
      List2.msetHeap (List2.merge ho1 ho2) =
        List2.msetHeap ho1 + List2.msetHeap ho2) ∧
    (∀ (ho1 ho2 : List2.Heap α), List2.invar ho1 → List2.invar ho2 →
      List2.invar (List2.merge ho1 ho2)) :=
  List2.priority_queue_merge

-- Check the `List2` specification in the locale's form.
example :
    PriorityQueueMergeSpec (List2.empty : List2.Heap α) List2.isEmpty
      List2.merge List2.insert List2.delMin List2.getMin List2.invar
      List2.msetHeap :=
  List2.priority_queue_merge_locale

-- Check the `List2` specification in the book's form.
example :
    PriorityQueueSpec (List2.empty : List2.Heap α) List2.merge List2.insert
      List2.delMin List2.getMin List2.invar List2.msetHeap :=
  List2.priority_queue_merge_book

-- Check the complete Exercise 23.1 statements.
example (hs : List (List2.Hp α)) :
    List2.mergePairs hs = List2.pass2 (List2.pass1 hs) :=
  List2.mergePairs_eq hs

example (hs : List (List2.Hp α)) :
    List2.TmergePairs hs ≤ List2.Tpass1 hs + List2.Tpass2 (List2.pass1 hs) :=
  List2.mergePairs_time_le hs

example (hs : List (List2.Hp α)) :
    List2.Tpass2 (List2.pass1 hs) + List2.Tpass1 hs = hs.length + 2 :=
  List2.Tpass2_pass1_add_Tpass1 hs

-- Check the complete `Tree` correctness statements.
example {h1 h2 : Tree.BTree α} (h1r : Tree.isRoot h1) (h2r : Tree.isRoot h2) :
    Tree.msetTree (Tree.merge h1 h2) = Tree.msetTree h1 + Tree.msetTree h2 :=
  Tree.mset_merge h1r h2r

example {t : Tree.BTree α} (hr : Tree.isRoot t) (hp : Tree.pheap t) :
    Tree.pheap (Tree.delMin t) :=
  Tree.pheap_delMin hr hp

example {t : Tree.BTree α} {x : α} (hr : Tree.isRoot t)
    (hx : Tree.getMin t = some x) :
    Tree.msetTree (Tree.delMin t) = Tree.msetTree t - {x} :=
  Tree.mset_delMin x hr hx

-- Check the `getMin` definedness clause for each variant.
example {ho : List2.Heap α} (hne : List2.msetHeap ho ≠ 0) :
    ∃ x, List2.getMin ho = some x :=
  List2.getMin_defined ho hne

example {t : Tree.BTree α} (hne : Tree.msetTree t ≠ 0) :
    ∃ x, Tree.getMin t = some x :=
  Tree.getMin_defined t hne

example {h : List1.Heap α} (hne : List1.msetHeap h ≠ 0) :
    ∃ x, List1.getMin h = some x :=
  List1.getMin_defined h hne

-- Check the `Tree` specification in the locale's form.
example :
    PriorityQueueMergeSpec (Tree.BTree.leaf : Tree.BTree α) Tree.isEmpty
      Tree.merge Tree.insert Tree.delMin Tree.getMin
      (fun t => Tree.isRoot t ∧ Tree.pheap t) Tree.msetTree :=
  Tree.priority_queue_merge_locale

-- Check the `Tree` specification in the book's form.
example :
    PriorityQueueSpec (Tree.BTree.leaf : Tree.BTree α) Tree.merge Tree.insert
      Tree.delMin Tree.getMin (fun t => Tree.isRoot t ∧ Tree.pheap t)
      Tree.msetTree :=
  Tree.priority_queue_merge_book

-- Check the complete `List1` correctness statements.
example (h1 h2 : List1.Heap α) :
    List1.msetHeap (List1.merge h1 h2) =
      List1.msetHeap h1 + List1.msetHeap h2 :=
  List1.mset_merge h1 h2

example {h : List1.Heap α} (hp : List1.pheap h) :
    List1.pheap (List1.delMin h) :=
  List1.pheap_delMin hp

example {h : List1.Heap α} {x : α} (hx : List1.getMin h = some x) :
    List1.msetHeap (List1.delMin h) = List1.msetHeap h - {x} :=
  List1.mset_delMin hx

-- Check the `List1` specification in the locale's form.
example :
    PriorityQueueMergeSpec (List1.Heap.empty : List1.Heap α) List1.isEmpty
      List1.merge List1.insert List1.delMin List1.getMin List1.pheap
      List1.msetHeap :=
  List1.priority_queue_merge_locale

-- Check the `List1` specification in the book's form.
example :
    PriorityQueueSpec (List1.Heap.empty : List1.Heap α) List1.merge
      List1.insert List1.delMin List1.getMin List1.pheap List1.msetHeap :=
  List1.priority_queue_merge_book

end PairingHeapAPITests

end Cslib.Algorithms.Lean
