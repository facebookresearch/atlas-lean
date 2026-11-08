/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SinglyLinkedList

/-!
# Tests for the singly linked-list API

These client examples exercise empty and singleton operations, tail deletion, aliased
insertion, duplicate first-match search, and fuel boundaries through the public executable
and correctness API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SinglyLinkedListTests

open Cslib.Algorithms.Lean.SinglyLinkedList

/-- A four-cell pool: `0 -> 1 -> 2` carrying `10, 20, 20`, plus detached cell `3`. -/
public def store3 : Vector (Option (Node Nat (Fin 4))) 4 :=
  #v[some ⟨10, some 1⟩, some ⟨20, some 2⟩, some ⟨20, none⟩, some ⟨99, none⟩]

example : contents store3 [0, 1, 2] = [some 10, some 20, some 20] := by
  decide

example : contents store3 ([] : List (Fin 4)) = [] := by
  decide

-- Duplicate payloads: search returns the first match.
example : search store3 (some 0) 20 = some 1 := by
  decide

example : search store3 (some 0) 10 = some 0 := by
  decide

example : search store3 (some 0) 30 = none := by
  decide

-- Empty header: nothing is found.
example : search store3 none 10 = none := by
  decide

-- Fuel boundaries for `searchAux`.
example : searchAux store3 20 0 (some 0) = none := by
  decide

example : searchAux store3 20 1 (some 0) = none := by
  decide

example : searchAux store3 20 2 (some 0) = some 1 := by
  decide

example : searchAux store3 10 1 (some 0) = some 0 := by
  decide

example : searchAux store3 20 3 (some 2) = some 2 := by
  decide

-- Prepend onto a nonempty list and onto the empty list (singleton result).
public def prepended :=
  prepend store3 (some 0) 3 (by decide)

example : prepended.2 = some 3 := by
  decide

example : contents prepended.1 [3, 0, 1, 2] = [some 99, some 10, some 20, some 20] := by
  decide

example : search prepended.1 prepended.2 10 = some 0 := by
  decide

public def prependedEmpty :=
  prepend store3 none 3 (by decide)

example : prependedEmpty.2 = some 3 := by
  decide

example : search prependedEmpty.1 prependedEmpty.2 99 = some 3 := by
  decide

example : search prependedEmpty.1 prependedEmpty.2 10 = none := by
  decide

-- Insertion after the head, and aliased insertion (`y = x` self-links the node).
public def inserted : Vector (Option (Node Nat (Fin 4))) 4 :=
  insertAfter store3 0 3 (by decide) (by decide)

example : contents inserted [0, 3, 1, 2] = [some 10, some 99, some 20, some 20] := by
  decide

example : inserted.get 0 = some ⟨10, some 3⟩ := by
  decide

example : inserted.get 3 = some ⟨99, some 1⟩ := by
  decide

example : search inserted (some 0) 99 = some 3 := by
  decide

public def insertedAlias : Vector (Option (Node Nat (Fin 4))) 4 :=
  insertAfter store3 0 0 (by decide) (by decide)

example : insertedAlias.get 0 = some ⟨10, some 0⟩ := by
  decide

example : insertedAlias.get 1 = some ⟨20, some 2⟩ := by
  decide

-- Insertion after the tail.
public def insertedTail : Vector (Option (Node Nat (Fin 4))) 4 :=
  insertAfter store3 2 3 (by decide) (by decide)

example : insertedTail.get 2 = some ⟨20, some 3⟩ := by
  decide

example : insertedTail.get 3 = some ⟨99, none⟩ := by
  decide

-- Head deletion on empty, singleton, and nonempty lists; the pool is unchanged.
example : (deleteHead store3 none).1 = store3 :=
  rfl

example : (deleteHead store3 none).2 = none := by
  decide

example : (deleteHead store3 (some 2)).2 = none := by
  decide

example : (deleteHead store3 (some 0)).2 = some 1 := by
  decide

example : search (deleteHead store3 (some 0)).1 (deleteHead store3 (some 0)).2 10 = none := by
  decide

-- Successor deletion in the middle, and a no-op splice at the tail.
public def deletedMiddle : Vector (Option (Node Nat (Fin 4))) 4 :=
  deleteAfter store3 0 (by decide)

example : deletedMiddle.get 0 = some ⟨10, some 2⟩ := by
  decide

example : contents deletedMiddle [0, 2] = [some 10, some 20] := by
  decide

example : deletedMiddle.get 1 = some ⟨20, some 2⟩ := by
  decide

public def deletedTail : Vector (Option (Node Nat (Fin 4))) 4 :=
  deleteAfter store3 2 (by decide)

example : deletedTail.toList = store3.toList := by
  decide

example : contents deletedTail [0, 1, 2] = [some 10, some 20, some 20] := by
  decide

public def deletedBeforeTail : Vector (Option (Node Nat (Fin 4))) 4 :=
  deleteAfter store3 1 (by decide)

example : deletedBeforeTail.get 1 = some ⟨20, none⟩ := by
  decide

-- Public theorem API, including the search theorems with no capacity hypothesis.
example {capacity : Nat}
    {store : Vector (Option (Node Nat (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) : ids.length ≤ capacity :=
  represents_length_le_capacity rep

example {capacity : Nat}
    (store : Vector (Option (Node Nat (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (target : Nat) (ids : List (Fin capacity))
    (rep : Represents store head ids) :
    search store head target =
      ids.find? (fun i => decide ((store.get i).map Node.payload = some target)) :=
  search_eq_find? store head target ids rep

example {capacity : Nat}
    (store : Vector (Option (Node Nat (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (target : Nat) (ids : List (Fin capacity))
    (rep : Represents store head ids) {x : Fin capacity}
    (h : search store head target = some x) :
    x ∈ ids ∧ (store.get x).map Node.payload = some target :=
  search_eq_some store head target ids rep h

example {capacity : Nat}
    (store : Vector (Option (Node Nat (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (target : Nat) (ids : List (Fin capacity))
    (rep : Represents store head ids) :
    search store head target = none ↔
      ∀ i ∈ ids, (store.get i).map Node.payload ≠ some target :=
  search_eq_none_iff store head target ids rep

example {capacity : Nat}
    (store : Vector (Option (Node Nat (Fin capacity))) capacity) :
    Represents store none ([] : List (Fin capacity)) :=
  represents_nil store

example {capacity : Nat}
    (store : Vector (Option (Node Nat (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity))
    (rep : Represents store head ids) :
    Represents (deleteHead store head).1 (deleteHead store head).2 ids.tail :=
  deleteHead_represents store head ids rep

end Cslib.Algorithms.Lean.SinglyLinkedListTests
