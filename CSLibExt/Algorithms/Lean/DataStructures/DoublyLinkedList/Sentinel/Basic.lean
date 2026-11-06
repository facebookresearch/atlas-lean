/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Basic

/-!
# Circular doubly-linked lists with an allocated sentinel

CLRS fourth edition, section 10.2, printed pages 261–262. The sentinel replaces
NIL and links the first and last data nodes, or links to itself for an empty list.
The same canonical node pool supports several disjoint represented circles.
Payloads are unrestricted; the sentinel is an allocated node, not another carrier.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.DoublyLinkedList

universe u

/-- **Circular doubly linked list with a sentinel.** Let $S$ be a store of $n$ slots indexed by
$\{0, \dots, n-1\}$, each either empty or holding a node with a payload and optional next and
previous indices. The store $S$ represents a circular list with sentinel $s$ and data nodes
$x_1, \dots, x_k$ (a list of indices) when the $x_i$ are pairwise distinct and all differ from
$s$; slot $s$ holds a node whose next index is $x_1$ and whose previous index is $x_k$ (both
are $s$ when $k = 0$); and for every $i$ with $1 \le i \le k$, slot $x_i$ holds a node whose
previous index is $x_{i-1}$ and whose next index is $x_{i+1}$, where $x_0 = x_{k+1} = s$. -/
def CircularRepresents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (s : Fin capacity) (ids : List (Fin capacity)) : Prop :=
  ids.Nodup ∧ s ∉ ids ∧
    (∃ sentinel, store.get s = some sentinel ∧
      sentinel.next = some (ids.headD s) ∧ sentinel.prev = some (ids.getLastD s)) ∧
    ∀ (before : List (Fin capacity)) (a : Fin capacity) (after : List (Fin capacity)),
      ids = before ++ a :: after → ∃ node, store.get a = some node ∧
        node.prev = some (before.getLastD s) ∧ node.next = some (after.headD s)

/-- **Empty circular list with a sentinel.** Let $S$ be a store of $n$ slots indexed by
$\{0, \dots, n-1\}$, each either empty or holding a node with a payload and optional next and
previous indices, and let $s$ be an index. Then $S$ represents the empty circular list with
sentinel $s$ if and only if slot $s$ holds a node whose next index and previous index are both
$s$. -/
public theorem CircularRepresents_nil {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (s : Fin capacity) :
    CircularRepresents store s [] ↔
      ∃ sentinel, store.get s = some sentinel ∧
        sentinel.next = some s ∧ sentinel.prev = some s := by
  constructor
  · intro h
    exact h.2.2.1
  · intro h
    refine ⟨by simp, by simp, h, ?_⟩
    intro before a after he
    have impossible : False := by simpa using congrArg List.length he
    exact impossible.elim

end Cslib.Algorithms.Lean.DoublyLinkedList
