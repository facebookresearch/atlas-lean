/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`thys/Skew_Heap/Skew_Heap.thy` (Archive of Formal Proofs, entry `Skew Heap`, https://isa-afp.org/entries/Skew_Heap.html):
Copyright (c) 2014 Tobias Nipkow. All rights reserved.
Licensed under the BSD License.
Authors: Tobias Nipkow
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SkewHeap.Basic
public import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

/-!
# The priority-queue ADTs

The ADTs `Priority_Queue` and `Priority_Queue_Merge` (book §14.1,
Figs. 14.1-14.2) as structures, and the proof that skew heaps
satisfy them (`skewPQ`, `skewPQMerge`) — the formal version of
§22.1's claim that it is "straightforward to prove the correctness
of the implementation w.r.t. the ADT `Priority_Queue_Merge`".
`get_min` is `Option`-valued (partiality on the empty queue made
explicit), and the `del_min` clause is stated in the equivalent
additive form `mset (delMin q) + {m} = mset q` rather than the
book's `mset q - {#get_min q#}`.

Source: book section 14.1, Figs. 14.1-14.2 (the `Priority_Queue`
and `Priority_Queue_Merge` ADTs), as interpreted for skew heaps in
the AFP entry `Skew Heap`, `thys/Skew_Heap/Skew_Heap.thy`
(https://isa-afp.org/entries/Skew_Heap.html). The structures and
proofs are re-established in Lean; Isabelle-derived names are kept
for traceability.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace SkewHeap

variable {α : Type u} [LinearOrder α]


/- ## ADT `Priority_Queue` / `Priority_Queue_Merge` (book §14.1, Figs. 14.1–14.2) -/

/-- ADT `Priority_Queue` (book Fig. 14.1): interface, abstraction
function `mset`, invariant `invar`, and the seven specification
clauses (`empty`, `empty-inv`, `insert`, `insert-inv`, `del_min`,
`del_min-inv`, `get_min`).

Two renderings of Isabelle/HOL in the book are made explicit here:
* The book's `get_min : 0q → 0a` is partial (unspecified on the
  empty queue); here it is `Option`-valued, and the `del_min` /
  `get_min` clauses are stated for `mset q ≠ 0`, exactly as in the
  book, with the minimum produced as `some m`.
* The book writes the `del_min` clause as
  `mset (del_min q) = mset q - {#get_min q#}` (remove one occurrence
  of the minimum). It is stated here in the equivalent additive form
  `mset (del_min q) + {m} = mset q`, which is the form the
  skew-heap proof produces directly (`mset_delMin_add`) and which
  avoids committing to a particular multiset-difference operation. -/
structure PriorityQueue (Q : Type u) (α : Type u) [LinearOrder α] where
  empty : Q
  insert : α → Q → Q
  delMin : Q → Q
  getMin : Q → Option α
  mset : Q → Multiset α
  invar : Q → Prop
  mset_empty : mset empty = 0
  invar_empty : invar empty
  mset_insert : ∀ {x q}, invar q → mset (insert x q) = mset q + {x}
  invar_insert : ∀ {x q}, invar q → invar (insert x q)
  mset_delMin : ∀ {q}, invar q → mset q ≠ 0 →
    ∃ m, getMin q = some m ∧ mset (delMin q) + {m} = mset q
  invar_delMin : ∀ {q}, invar q → mset q ≠ 0 → invar (delMin q)
  getMin_spec : ∀ {q}, invar q → mset q ≠ 0 →
    ∃ m, getMin q = some m ∧ m ∈ mset q ∧ ∀ x ∈ mset q, m ≤ x

/-- ADT `Priority_Queue_Merge` (book Fig. 14.2): `Priority_Queue`
plus `merge` and its two specification clauses (`merge`,
`merge-inv`). -/
structure PriorityQueueMerge (Q : Type u) (α : Type u) [LinearOrder α] where
  toPQ : PriorityQueue Q α
  merge : Q → Q → Q
  mset_merge : ∀ {q1 q2}, toPQ.invar q1 → toPQ.invar q2 →
    toPQ.mset (merge q1 q2) = toPQ.mset q1 + toPQ.mset q2
  invar_merge : ∀ {q1 q2}, toPQ.invar q1 → toPQ.invar q2 →
    toPQ.invar (merge q1 q2)

/-- Skew heaps satisfy ADT `Priority_Queue`, with `invar = heap`
and `mset = mset_tree`, as in §14.1. -/
def skewPQ : PriorityQueue (Tree α) α where
  empty := .leaf
  insert := insert
  delMin := delMin
  getMin := getMin
  mset := toMultiset
  invar := heap
  mset_empty := toMultiset_leaf
  invar_empty := heap_leaf
  mset_insert := fun {x q} _ => by rw [mset_insert]; exact add_comm _ _
  invar_insert := fun {x q} h => heap_insert x h
  mset_delMin := fun {q} _ hne => by
    cases q with
    | leaf => simp [toMultiset_leaf] at hne
    | node l a r => exact ⟨a, rfl, mset_delMin_add l a r⟩
  invar_delMin := fun {q} h _ => heap_delMin h
  getMin_spec := fun {q} h hne => by
    cases q with
    | leaf => simp [toMultiset_leaf] at hne
    | node l a r =>
      refine ⟨a, rfl, ?_, ?_⟩
      · simp [toMultiset_node]
      · intro x hx
        exact heap_all_ge_mset h x hx

/-- Skew heaps satisfy ADT `Priority_Queue_Merge` — the formal
version of §22.1's claim that it is "straightforward to prove the
correctness of the implementation w.r.t. the ADT
`Priority_Queue_Merge`" (from `size_merge`/`mset_merge`/`heap_merge`
for `merge`, plus `skewPQ` for the other operations). -/
def skewPQMerge : PriorityQueueMerge (Tree α) α where
  toPQ := skewPQ
  merge := merge
  mset_merge := fun {_q1 _q2} _ _ => mset_merge _q1 _q2
  invar_merge := fun {_q1 _q2} h1 h2 => heap_merge h1 h2


end SkewHeap

end Cslib.Algorithms.Lean
