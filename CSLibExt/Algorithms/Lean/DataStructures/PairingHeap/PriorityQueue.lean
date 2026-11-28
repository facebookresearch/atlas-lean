/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Order.Bounds.Defs

/-!
# The priority-queue specifications (book §14.1, Figs. 14.1–14.2)

The `Priority_Queue_Merge` specification as conjunctions: the Isabelle
locale's form (`HOL-Data_Structures.Priority_Queue_Specs`, 10
assumptions, including `is_empty`) and the book's form (Chapter 14,
Figures 14.1–14.2, exactly 9 properties, no `is_empty` clause). The
three pairing-heap variants each discharge both forms (see
`PairingHeap.List2`, `PairingHeap.Tree`, `PairingHeap.List1`).

Two renderings of Isabelle/HOL in the book are made explicit here:
* The book's `get_min` is partial (unspecified on the empty queue);
  here it is `Option`-valued, and the `del_min` / `get_min` clauses are
  stated for `mset q ≠ 0`, exactly as in the book, with the minimum
  produced as `some x`.
* The `del_min` / `get_min` clauses are vacuous when `getMin q = none`,
  so an implementation whose `getMin` always returns `none` would
  otherwise satisfy them. Both specs therefore add a definedness
  clause, `mset q ≠ 0 → ∃ x, getMin q = some x`, which is not in the
  Isabelle locale or the book: it is the totalized form of the fact
  that the book's partial `get_min` is defined on nonempty queues.
* The book writes the `del_min` clause as
  `mset (del_min q) = mset q - {#get_min q#}` (remove one occurrence
  of the minimum). It is stated here in that subtractive form, which is
  the form the pairing-heap proofs produce directly. (The sibling
  `SkewHeap` port instead uses the equivalent additive form
  `mset (delMin q) + {m} = mset q`.)
* The book's `Min_mset m` is `Min (set_mset m)` (Chapter 14,
  introduction): the least element of the *set* of multiset elements —
  rendered here, as in the conversion, by `IsLeast {y | y ∈ mset q} x`.

Ported from the Chapter 23 Lean conversion in
`converted_proofs/ch23/lean/Chapter23.lean`, itself a conversion of the
Isabelle/HOL sources: the AFP entries `Pairing_Heap`
(`Pairing_Heap_List1.thy`, `Pairing_Heap_List2.thy`,
`Pairing_Heap_Tree.thy`) and `Amortized_Complexity`
(`Pairing_Heap_List2_Analysis.thy`, `Pairing_Heap_Tree_Analysis2.thy`),
and Tobias Nipkow (ed.), *Functional Data Structures and Algorithms:
A Proof Assistant Approach*, Chapter 23 (Pairing Heaps, pp. 257–264).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace PairingHeap

variable {α : Type u}

/-- The `Priority_Queue_Merge` specification in the Isabelle locale's
form: the locale's 10 assumptions (the `invar` hypotheses are kept,
`isEmpty` is used, `mset_insert` is stated as `mset + {x}`, and
`mset_get_min` is the `IsLeast` form), plus the definedness clause
`mset q ≠ 0 → ∃ x, getMin q = some x` described in the module doc.
The `del_min` clause is the book's subtractive form. -/
def PriorityQueueMergeSpec {S : Type u} [LinearOrder α]
    (empty : S) (isEmpty : S → Prop) (merge : S → S → S)
    (insert : α → S → S) (delMin : S → S) (getMin : S → Option α)
    (invar : S → Prop) (mset : S → Multiset α) : Prop :=
  (mset empty = 0) ∧
  (∀ q : S, invar q → (isEmpty q ↔ mset q = 0)) ∧
  (∀ (x : α) (q : S), invar q → mset (insert x q) = mset q + {x}) ∧
  (∀ (q : S) (x : α), invar q → mset q ≠ 0 → getMin q = some x →
    mset (delMin q) = mset q - {x}) ∧
  (∀ (q : S) (x : α), invar q → mset q ≠ 0 → getMin q = some x →
    IsLeast {y | y ∈ mset q} x) ∧
  (∀ q : S, mset q ≠ 0 → ∃ x, getMin q = some x) ∧
  invar empty ∧
  (∀ (x : α) (q : S), invar q → invar (insert x q)) ∧
  (∀ q : S, invar q → mset q ≠ 0 → invar (delMin q)) ∧
  (∀ (q1 q2 : S), invar q1 → invar q2 →
    mset (merge q1 q2) = mset q1 + mset q2) ∧
  (∀ (q1 q2 : S), invar q1 → invar q2 → invar (merge q1 q2))

/-- The `Priority_Queue_Merge` specification in the book's form: Chapter 14,
Figures 14.1–14.2. The book's 9 properties, in the book's order and with
the book's `invar` hypotheses: (empty), (empty-inv), (insert),
(insert-inv), (del_min), (del_min-inv), (get_min), and the two `Merge`
properties, plus the definedness clause
`mset q ≠ 0 → ∃ x, getMin q = some x` described in the module doc.
The book has **no** `is_empty` property — the Isabelle locale added one —
so there is no `isEmpty` conjunct here. -/
def PriorityQueueSpec {S : Type u} [LinearOrder α]
    (empty : S) (merge : S → S → S)
    (insert : α → S → S) (delMin : S → S) (getMin : S → Option α)
    (invar : S → Prop) (mset : S → Multiset α) : Prop :=
  (mset empty = 0) ∧
  invar empty ∧
  (∀ (x : α) (q : S), invar q → mset (insert x q) = mset q + {x}) ∧
  (∀ (x : α) (q : S), invar q → invar (insert x q)) ∧
  (∀ (q : S) (x : α), invar q → mset q ≠ 0 → getMin q = some x →
    mset (delMin q) = mset q - {x}) ∧
  (∀ q : S, invar q → mset q ≠ 0 → invar (delMin q)) ∧
  (∀ (q : S) (x : α), invar q → mset q ≠ 0 → getMin q = some x →
    IsLeast {y | y ∈ mset q} x) ∧
  (∀ q : S, mset q ≠ 0 → ∃ x, getMin q = some x) ∧
  (∀ (q1 q2 : S), invar q1 → invar q2 →
    mset (merge q1 q2) = mset q1 + mset q2) ∧
  (∀ (q1 q2 : S), invar q1 → invar q2 → invar (merge q1 q2))

end PairingHeap

end Cslib.Algorithms.Lean
