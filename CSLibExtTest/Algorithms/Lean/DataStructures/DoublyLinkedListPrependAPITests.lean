/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Basic

/-! Ordinary-import consumers for the doubly-linked list prepend API. -/

set_option autoImplicit false

open Cslib.Algorithms.Lean.DoublyLinkedList

universe u

#check @Node
#check @Represents
#check @listPrepend
#check @listPrepend_head
#check @listPrepend_time
#check @listPrepend_ret
#check @listPrepend_get
#check @listPrepend_frame
#check @listPrepend_allocated
#check @listPrepend_payload
#check @listPrepend_node
#check @listPrepend_oldHead
#check @listPrepend_represents
#check @listPrepend_disjoint_represents
#check @listPrepend_time_le

example {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) :
    Cslib.Algorithms.Lean.TimeM Nat
      (Vector (Option (Node α (Fin capacity))) capacity × Option (Fin capacity)) :=
  listPrepend store head x hx hh

example : (listPrepend
    (#v[some ⟨25, some 0, some 0⟩] : Vector (Option (Node Nat (Fin 1))) 1)
    none 0 (by rfl) (by intro h hh; cases hh)).ret =
    (#v[some ⟨25, none, none⟩], some 0) := rfl

example {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome)
    (ids : List (Fin capacity)) (rep : Represents store head ids) (fresh : x ∉ ids) :
    Represents (listPrepend store head x hx hh).ret.1
      (listPrepend store head x hx hh).ret.2 (x :: ids) :=
  listPrepend_represents store head x hx hh ids rep fresh

example {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) (z : Fin capacity) :
    ((listPrepend store head x hx hh).ret.1.get z).map Node.payload =
      (store.get z).map Node.payload :=
  listPrepend_payload store head x hx hh z

private def clrsStore : Vector (Option (Node (Nat × String) (Fin 10))) 10 :=
  #v[some ⟨(4, "four"), some 6, some 4⟩,
    some ⟨(9, "nine"), some 4, none⟩,
    some ⟨(9, "other-nine-a"), some 5, none⟩,
    some ⟨(25, "new-twenty-five"), some 2, some 9⟩,
    some ⟨(16, "sixteen"), some 0, some 1⟩,
    some ⟨(9, "other-nine-b"), none, some 2⟩,
    some ⟨(1, "one"), none, some 0⟩,
    none,
    some ⟨(25, "second-twenty-five"), some 9, some 2⟩,
    some ⟨(25, "foreign-twenty-five"), some 9, some 9⟩]

private theorem clrsRep : Represents clrsStore (some 1) [1, 4, 0, 6] := by
  refine ⟨by decide, rfl, ?_⟩
  intro i hi
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    simp only [List.length_cons, List.length_nil] at hi
    omega
  rcases casesI with rfl | rfl | rfl | rfl
  · exact ⟨⟨(9, "nine"), some 4, none⟩, rfl, rfl, rfl⟩
  · exact ⟨⟨(16, "sixteen"), some 0, some 1⟩, rfl, rfl, rfl⟩
  · exact ⟨⟨(4, "four"), some 6, some 4⟩, rfl, rfl, rfl⟩
  · exact ⟨⟨(1, "one"), none, some 0⟩, rfl, rfl, rfl⟩

private theorem otherRep : Represents clrsStore (some 2) [2, 5] := by
  refine ⟨by decide, rfl, ?_⟩
  intro i hi
  have casesI : i = 0 ∨ i = 1 := by
    simp only [List.length_cons, List.length_nil] at hi
    omega
  rcases casesI with rfl | rfl
  · exact ⟨⟨(9, "other-nine-a"), some 5, none⟩, rfl, rfl, rfl⟩
  · exact ⟨⟨(9, "other-nine-b"), none, some 2⟩, rfl, rfl, rfl⟩

example : Represents (listPrepend clrsStore (some 1) 3 (by rfl) (by
    intro h he; cases Option.some.inj he; rfl)).ret.1 (some 3) [3, 1, 4, 0, 6] :=
  listPrepend_represents clrsStore (some 1) 3 (by rfl) (by
    intro h he; cases Option.some.inj he; rfl) [1, 4, 0, 6] clrsRep (by decide)

example : Represents (listPrepend clrsStore (some 1) 3 (by rfl) (by
    intro h he; cases Option.some.inj he; rfl)).ret.1 (some 2) [2, 5] :=
  listPrepend_disjoint_represents clrsStore (some 1) 3 (by rfl) (by
    intro h he; cases Option.some.inj he; rfl) (some 2) [2, 5] otherRep (by decide) (by
      intro h he; cases Option.some.inj he; decide)

example : ¬ Represents
    (#v[some ⟨25, some 0, some 0⟩] : Vector (Option (Node Nat (Fin 1))) 1)
    (some 0) [0] := by
  intro rep
  obtain ⟨node, cell, prev, _⟩ := rep.2.2 0 (by decide)
  have eqNode : node = ⟨25, some 0, some 0⟩ := Option.some.inj cell.symm
  subst node
  cases prev
