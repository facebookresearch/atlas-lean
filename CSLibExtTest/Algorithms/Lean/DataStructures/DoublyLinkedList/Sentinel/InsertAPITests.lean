/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Sentinel.Insert

/-! Ordinary nine-role generic API consumers; no import-all or private helper. -/

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.DoublyLinkedList
universe u

#check @sentinelInsert

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    (sentinelInsert store x y hx hy hn hs).time = 4 :=
  sentinelInsert_time store x y hx hy hn hs

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    let updated := store.set x.val (some { (store.get x).get hx with
      next := ((store.get y).get hy).next, prev := some y }) x.isLt
    let z := ((store.get y).get hy).next.get hn
    let backlinked := updated.set z.val
      ((updated.get z).map fun (node : Node α (Fin n)) =>
        { node with prev := some x }) z.isLt
    (sentinelInsert store x y hx hy hn hs).ret = backlinked.set y.val
      ((backlinked.get y).map fun (node : Node α (Fin n)) =>
        { node with next := some x }) y.isLt :=
  sentinelInsert_ret store x y hx hy hn hs

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    let first := if x = z then some { (store.get x).get hx with
      next := ((store.get y).get hy).next, prev := some y } else store.get z
    let second := if ((store.get y).get hy).next = some z then
      first.map (fun (node : Node α (Fin n)) => { node with prev := some x }) else first
    (sentinelInsert store x y hx hy hn hs).ret.get z =
      if y = z then second.map (fun (node : Node α (Fin n)) =>
        { node with next := some x }) else second :=
  sentinelInsert_get store x y z hx hy hn hs

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome)
    (hxz : x ≠ z) (hyz : y ≠ z) (hsz : ((store.get y).get hy).next ≠ some z) :
    (sentinelInsert store x y hx hy hn hs).ret.get z = store.get z :=
  sentinelInsert_frame store x y z hx hy hn hs hxz hyz hsz

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    ((sentinelInsert store x y hx hy hn hs).ret.get z).isSome =
      (store.get z).isSome :=
  sentinelInsert_allocated store x y z hx hy hn hs

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    ((sentinelInsert store x y hx hy hn hs).ret.get z).map Node.payload =
      (store.get z).map Node.payload :=
  sentinelInsert_payload store x y z hx hy hn hs

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y s : Fin n)
    (ids before after : List (Fin n))
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome)
    (hc : CircularRepresents store s ids)
    (hSplit : ids = before ++ after) (hPosition : y = before.getLastD s)
    (hFreshSentinel : x ≠ s) (hFreshData : x ∉ ids) :
    CircularRepresents (sentinelInsert store x y hx hy hn hs).ret s
      (before ++ x :: after) :=
  sentinelInsert_circular store x y s ids before after hx hy hn hs hc hSplit hPosition hFreshSentinel hFreshData

example {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y s t : Fin n)
    (ids before after other : List (Fin n))
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome)
    (hc : CircularRepresents store s ids)
    (hSplit : ids = before ++ after) (hPosition : y = before.getLastD s)
    (hcOther : CircularRepresents store t other)
    (hDisjoint : List.Disjoint (s :: ids) (t :: other))
    (hFreshSentinel : x ≠ t) (hFreshData : x ∉ other) :
    CircularRepresents (sentinelInsert store x y hx hy hn hs).ret t other :=
  sentinelInsert_disjoint_circular store x y s t ids before after other hx hy hn hs hc hSplit hPosition hcOther hDisjoint hFreshSentinel hFreshData
