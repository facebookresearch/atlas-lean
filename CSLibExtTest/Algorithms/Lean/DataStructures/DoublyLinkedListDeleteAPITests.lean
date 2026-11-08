/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Delete

/-!
# Ordinary public deletion API tests
-/

open Cslib.Algorithms.Lean.DoublyLinkedList

open Cslib.Algorithms.Lean

universe u

section

variable {α : Type u} {capacity : Nat}
  (store : Vector (Option (Node α (Fin capacity))) capacity)
  (head : Option (Fin capacity)) (x : Fin capacity)
  (hx : (store.get x).isSome)
  (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
  (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)

example : (listDelete store head x hx hp hn).time =
    if ((store.get x).get hx).next.isSome then 4 else 3 :=
  listDelete_time store head x hx hp hn

example : (listDelete store head x hx hp hn).ret.2 =
    if ((store.get x).get hx).prev.isSome then head else ((store.get x).get hx).next :=
  listDelete_head store head x hx hp hn

example :
    let originalX := (store.get x).get hx
    let carried := match originalX.prev with
      | none => store
      | some p => store.set p.val
          ((store.get p).map fun node => { node with next := originalX.next }) p.isLt
    (listDelete store head x hx hp hn).ret =
      (match originalX.next with
       | none => carried
       | some n => carried.set n.val
           ((carried.get n).map fun node => { node with prev := originalX.prev }) n.isLt,
       if originalX.prev.isSome then head else originalX.next) :=
  listDelete_ret store head x hx hp hn

example (z : Fin capacity) :
    (listDelete store head x hx hp hn).ret.1.get z =
      let originalX := (store.get x).get hx
      let carried := if originalX.prev = some z then
        (store.get z).map fun node => { node with next := originalX.next } else store.get z
      if originalX.next = some z then
        carried.map fun node => { node with prev := originalX.prev } else carried :=
  listDelete_get store head x hx hp hn z

example (z : Fin capacity)
    (hzp : ((store.get x).get hx).prev ≠ some z)
    (hzn : ((store.get x).get hx).next ≠ some z) :
    (listDelete store head x hx hp hn).ret.1.get z = store.get z :=
  listDelete_frame store head x hx hp hn z hzp hzn

example (z : Fin capacity) :
    ((listDelete store head x hx hp hn).ret.1.get z).isSome = (store.get z).isSome :=
  listDelete_allocated store head x hx hp hn z

example (z : Fin capacity) :
    ((listDelete store head x hx hp hn).ret.1.get z).map Node.payload =
      (store.get z).map Node.payload :=
  listDelete_payload store head x hx hp hn z

example : (listDelete store head x hx hp hn).ret.1.get x = store.get x :=
  listDelete_deleted_record store head x hx hp hn

example (otherHead : Option (Fin capacity)) (otherIds : List (Fin capacity))
    (rep : Represents store otherHead otherIds)
    (disjointP : ∀ p, ((store.get x).get hx).prev = some p → p ∉ otherIds)
    (disjointN : ∀ n, ((store.get x).get hx).next = some n → n ∉ otherIds) :
    Represents (listDelete store head x hx hp hn).ret.1 otherHead otherIds :=
  listDelete_disjoint_represents store head x hx hp hn otherHead otherIds rep disjointP disjointN

example : (listDelete store head x hx hp hn).time ≤ 4 :=
  listDelete_time_le store head x hx hp hn

end

private def chainStore {α : Type u} (a b c : α) : Vector (Option (Node α (Fin 3))) 3 :=
  #v[some ⟨a, some 1, none⟩, some ⟨b, some 2, some 0⟩, some ⟨c, none, some 1⟩]

private lemma chainRep {α : Type u} (a b c : α) :
    Represents (chainStore a b c) (some 0) [0, 1, 2] := by
  refine ⟨by decide, rfl, ?_⟩
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by
    simp only [List.length_cons, List.length_nil] at hi
    omega
  rcases cases with h | h | h
  · subst i
    exact ⟨⟨a, some 1, none⟩, rfl, rfl, rfl⟩
  · subst i
    exact ⟨⟨b, some 2, some 0⟩, rfl, rfl, rfl⟩
  · subst i
    exact ⟨⟨c, none, some 1⟩, rfl, rfl, rfl⟩

example {α : Type u} (a b c : α) :
    let result := listDelete (chainStore a b c) (some 0) 0 (by rfl)
      (by intro p he; cases he) (by intro n he; cases Option.some.inj he; rfl)
    Represents result.ret.1 result.ret.2 [1, 2] :=
  listDelete_represents _ _ _ _ _ _ _ (chainRep a b c) (by decide)

example {α : Type u} (a b c : α) :
    let result := listDelete (chainStore a b c) (some 0) 1 (by rfl)
      (by intro p he; cases Option.some.inj he; rfl)
      (by intro n he; cases Option.some.inj he; rfl)
    Represents result.ret.1 result.ret.2 [0, 2] :=
  listDelete_represents _ _ _ _ _ _ _ (chainRep a b c) (by decide)

example {α : Type u} (a b c : α) :
    let result := listDelete (chainStore a b c) (some 0) 2 (by rfl)
      (by intro p he; cases Option.some.inj he; rfl) (by intro n he; cases he)
    Represents result.ret.1 result.ret.2 [0, 1] :=
  listDelete_represents _ _ _ _ _ _ _ (chainRep a b c) (by decide)

example {α : Type u} (a : α) :
    let store : Vector (Option (Node α (Fin 1))) 1 := #v[some ⟨a, none, none⟩]
    let result := listDelete store (some 0) 0 (by rfl)
      (by intro p he; cases he) (by intro n he; cases he)
    Represents result.ret.1 result.ret.2 [] := by
  apply listDelete_represents (ids := [0])
  · refine ⟨by decide, rfl, ?_⟩
    intro i hi
    have iz : i = 0 := by
      simp only [List.length_cons, List.length_nil] at hi
      omega
    subst i
    exact ⟨⟨a, none, none⟩, rfl, rfl, rfl⟩
  · decide

example {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (ids : List (Fin capacity)) (rep : Represents store head ids) (member : x ∈ ids) :
    Represents (listDelete store head x hx hp hn).ret.1
      (listDelete store head x hx hp hn).ret.2 (ids.erase x) :=
  listDelete_represents store head x hx hp hn ids rep member

#print axioms listDelete
#print axioms listDelete_time
#print axioms listDelete_head
#print axioms listDelete_ret
#print axioms listDelete_get
#print axioms listDelete_frame
#print axioms listDelete_allocated
#print axioms listDelete_payload
#print axioms listDelete_deleted_record
#print axioms listDelete_disjoint_represents
#print axioms listDelete_time_le
#print axioms listDelete_represents
