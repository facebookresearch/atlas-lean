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

/-- Allocated circular sentinel and exact links at every ordered data-node split. -/
def CircularRepresents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (s : Fin capacity) (ids : List (Fin capacity)) : Prop :=
  ids.Nodup ∧ s ∉ ids ∧
    (∃ sentinel, store.get s = some sentinel ∧
      sentinel.next = some (ids.headD s) ∧ sentinel.prev = some (ids.getLastD s)) ∧
    ∀ (before : List (Fin capacity)) (a : Fin capacity) (after : List (Fin capacity)),
      ids = before ++ a :: after → ∃ node, store.get a = some node ∧
        node.prev = some (before.getLastD s) ∧ node.next = some (after.headD s)

/-- The empty circle consists of an allocated self-linked sentinel. -/
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
