/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Insert

/-! Ordinary generic consumers of the nine LIST-INSERT roles. -/

set_option autoImplicit false

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.DoublyLinkedList

universe u

#check @listInsert

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    TimeM Nat (Vector (Option (Node α (Fin n))) n) := by
  exact listInsert store x y hx hy hs

#check @listInsert_time

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    (listInsert store x y hx hy hs).time =
      if ((store.get y).get hy).next.isSome then 5 else 4 := by
  exact listInsert_time store x y hx hy hs

#check @listInsert_ret

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    let updated := store.set x.val (some { (store.get x).get hx with
      next := ((store.get y).get hy).next, prev := some y }) x.isLt
    let backlinked := match ((store.get y).get hy).next with
      | none => updated
      | some z => updated.set z.val
          ((updated.get z).map fun (node : Node α (Fin n)) =>
            { node with prev := some x }) z.isLt
    (listInsert store x y hx hy hs).ret = backlinked.set y.val
      ((backlinked.get y).map fun (node : Node α (Fin n)) =>
        { node with next := some x }) y.isLt := by
  exact listInsert_ret store x y hx hy hs

#check @listInsert_get

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    let first := if x = z then some { (store.get x).get hx with
      next := ((store.get y).get hy).next, prev := some y } else store.get z
    let second := if ((store.get y).get hy).next = some z then
      first.map (fun (node : Node α (Fin n)) => { node with prev := some x }) else first
    (listInsert store x y hx hy hs).ret.get z =
      if y = z then second.map (fun (node : Node α (Fin n)) =>
        { node with next := some x }) else second := by
  exact listInsert_get store x y z hx hy hs

#check @listInsert_frame

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome)
    (hxz : x ≠ z) (hyz : y ≠ z) (hsz : ((store.get y).get hy).next ≠ some z) :
    (listInsert store x y hx hy hs).ret.get z = store.get z := by
  exact listInsert_frame store x y z hx hy hs hxz hyz hsz

#check @listInsert_allocated

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    ((listInsert store x y hx hy hs).ret.get z).isSome =
      (store.get z).isSome := by
  exact listInsert_allocated store x y z hx hy hs

#check @listInsert_payload

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    ((listInsert store x y hx hy hs).ret.get z).map Node.payload =
      (store.get z).map Node.payload := by
  exact listInsert_payload store x y z hx hy hs

#check @listInsert_represents

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x : Fin n)
    (head : Option (Fin n)) (ids : List (Fin n)) (rep : Represents store head ids)
    (fresh : x ∉ ids) (k : Nat) (hk : k < ids.length)
    (hx : (store.get x).isSome) (hy : (store.get ids[k]).isSome)
    (hs : ∀ z, ((store.get ids[k]).get hy).next = some z → (store.get z).isSome) :
    Represents (listInsert store x ids[k] hx hy hs).ret head
      (ids.insertIdx (k + 1) x) := by
  exact listInsert_represents store x head ids rep fresh k hk hx hy hs

#check @listInsert_disjoint_represents

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x : Fin n)
    (head otherHead : Option (Fin n)) (ids otherIds : List (Fin n))
    (rep : Represents store head ids) (otherRep : Represents store otherHead otherIds)
    (disjoint : List.Disjoint ids otherIds) (freshOther : x ∉ otherIds)
    (k : Nat) (hk : k < ids.length) (hx : (store.get x).isSome)
    (hy : (store.get ids[k]).isSome)
    (hs : ∀ z, ((store.get ids[k]).get hy).next = some z → (store.get z).isSome) :
    Represents (listInsert store x ids[k] hx hy hs).ret otherHead otherIds := by
  exact listInsert_disjoint_represents store x head otherHead ids otherIds rep otherRep disjoint freshOther k hk hx hy hs
