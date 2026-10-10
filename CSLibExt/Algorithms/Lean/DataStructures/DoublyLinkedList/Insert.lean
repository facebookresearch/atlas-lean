/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Basic
import Mathlib.Data.List.InsertIdx
import Init.Data.List.Perm

/-!
# Doubly-linked list insertion with pointer-event costs

CLRS fourth edition, section 10.2, printed page 261, LIST-INSERT.
An already allocated node is inserted after an allocated node in the source's
five-line order. Each update reads the carried store, including aliased targets.
Freshness is a representation-proof premise, not an execution guard.

The same computation counts executed pointer assignments and the successor NIL
test: four events at the tail, five otherwise. Indexing, record reads, erased
proofs and return are free. This is not physical RAM, persistent-copy, word/bit,
allocation, native execution-time or space complexity.

The return and pointwise equations preserve access-valid aliases. Canonical
`Represents` insertion uses `List.insertIdx`; another disjoint represented
list is preserved by the same store's frame theorem.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DoublyLinkedList

open Cslib.Algorithms.Lean

universe u

private lemma get_set {α : Type u} {n : Nat} (s : Vector α n)
    (i j : Fin n) (value : α) :
    (s.set i.val value i.isLt).get j = if i = j then value else s.get j := by
  change (s.set i.val value i.isLt)[j.val] = if i = j then value else s[j.val]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff]

private lemma allocated_set {α : Type u} {n : Nat} (s : Vector (Option α) n)
    (i : Fin n) (h : (s.get i).isSome) (value : α) (j : Fin n) :
    ((s.set i.val (some value) i.isLt).get j).isSome = (s.get j).isSome := by
  rw [get_set]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, Option.isSome_some]
    exact h.symm
  · simp only [hij, ite_false]

private lemma y_next_after_set {α : Type u} {n : Nat}
    (s : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (s.get x).isSome) (hy : (s.get y).isSome) :
    let value := { (s.get x).get hx with next := ((s.get y).get hy).next }
    let updated := s.set x.val (some value) x.isLt
    ((updated.get y).get ((allocated_set s x hx value y).trans hy)).next =
      ((s.get y).get hy).next := by
  dsimp only
  by_cases hxy : x = y
  · subst y
    simp only [get_set, ite_true, Option.get_some]
  · simp only [get_set, hxy, ite_false]

private lemma y_next_after_prev {α : Type u} {n : Nat}
    (s : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (s.get x).isSome) (hy : (s.get y).isSome) :
    let value := { (s.get x).get hx with prev := some y }
    let updated := s.set x.val (some value) x.isLt
    ((updated.get y).get ((allocated_set s x hx value y).trans hy)).next =
      ((s.get y).get hy).next := by
  dsimp only
  by_cases hxy : x = y
  · subst y
    simp only [get_set, ite_true, Option.get_some]
  · simp only [get_set, hxy, ite_false]

/-- Execution of all five source lines, with access validity only. -/
public def listInsert {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    TimeM Nat (Vector (Option (Node α (Fin n))) n) := do
  let oldY := (store.get y).get hy
  TimeM.tick 1
  let nextX := { (store.get x).get hx with next := oldY.next }
  let store1 := store.set x.val (some nextX) x.isLt
  have hx1 := (allocated_set store x hx nextX x).trans hx
  have hy1 := (allocated_set store x hx nextX y).trans hy
  TimeM.tick 1
  let prevX := { (store1.get x).get hx1 with prev := some y }
  let store2 := store1.set x.val (some prevX) x.isLt
  have hy2 := (allocated_set store1 x hx1 prevX y).trans hy1
  let currentY2 := (store2.get y).get hy2
  have nextPreserved : currentY2.next = oldY.next :=
    (y_next_after_prev store1 x y hx1 hy1).trans
      (y_next_after_set store x y hx hy)
  TimeM.tick 1
  match he : currentY2.next with
  | none =>
    TimeM.tick 1
    pure (store2.set y.val (some { currentY2 with next := some x }) y.isLt)
  | some z =>
    have hz := hs z (nextPreserved.symm.trans he)
    have hz1 := (allocated_set store x hx nextX z).trans hz
    have hz2 := (allocated_set store1 x hx1 prevX z).trans hz1
    let currentZ := (store2.get z).get hz2
    TimeM.tick 1
    let newZ := { currentZ with prev := some x }
    let store3 := store2.set z.val (some newZ) z.isLt
    have hy3 := (allocated_set store2 z hz2 newZ y).trans hy2
    let currentY3 := (store3.get y).get hy3
    TimeM.tick 1
    pure (store3.set y.val (some { currentY3 with next := some x }) y.isLt)

private lemma set_map_get {α : Type u} {n : Nat} (s : Vector (Option α) n)
    (i : Fin n) (h : (s.get i).isSome) (f : α → α) :
    s.set i.val (some (f ((s.get i).get h))) i.isLt =
      s.set i.val ((s.get i).map f) i.isLt := by
  exact congrArg (fun value => s.set i.val value i.isLt)
    (congrArg (Option.map f) (Option.some_get h))

private lemma first_two_store {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome) :
    let nextX := { (store.get x).get hx with next := ((store.get y).get hy).next }
    let store1 := store.set x.val (some nextX) x.isLt
    let hx1 := (allocated_set store x hx nextX x).trans hx
    store1.set x.val (some { (store1.get x).get hx1 with prev := some y }) x.isLt =
      store.set x.val
        (some { (store.get x).get hx with
          next := ((store.get y).get hy).next, prev := some y }) x.isLt := by
  dsimp only
  simp only [get_set, ite_true, Option.get_some, Vector.set_set]

/-- Exact source assignment/NIL-test events, including access-valid aliases. -/
public theorem listInsert_time {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    (listInsert store x y hx hy hs).time =
      if ((store.get y).get hy).next.isSome then 5 else 4 := by
  let oldY := (store.get y).get hy
  let nextX := { (store.get x).get hx with next := oldY.next }
  let store1 := store.set x.val (some nextX) x.isLt
  have hx1 := (allocated_set store x hx nextX x).trans hx
  have hy1 := (allocated_set store x hx nextX y).trans hy
  let prevX := { (store1.get x).get hx1 with prev := some y }
  let store2 := store1.set x.val (some prevX) x.isLt
  have hy2 := (allocated_set store1 x hx1 prevX y).trans hy1
  let currentY2 := (store2.get y).get hy2
  have hp : currentY2.next = oldY.next :=
    (y_next_after_prev store1 x y hx1 hy1).trans (y_next_after_set store x y hx hy)
  simp only [listInsert, TimeM.time_bind, TimeM.time_tick]
  split <;> rename_i he
  all_goals
    change currentY2.next = _ at he
    have hOld := hp.symm.trans he
    change ((store.get y).get hy).next = _ at hOld
    simp [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, hOld]

/-- Complete carried-store update; no freshness or representation premise. -/
public theorem listInsert_ret {α : Type u} {n : Nat}
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
  let oldY := (store.get y).get hy
  let nextX := { (store.get x).get hx with next := oldY.next }
  let store1 := store.set x.val (some nextX) x.isLt
  have hx1 := (allocated_set store x hx nextX x).trans hx
  have hy1 := (allocated_set store x hx nextX y).trans hy
  let prevX := { (store1.get x).get hx1 with prev := some y }
  let store2 := store1.set x.val (some prevX) x.isLt
  have hy2 := (allocated_set store1 x hx1 prevX y).trans hy1
  let currentY2 := (store2.get y).get hy2
  have hp : currentY2.next = oldY.next :=
    (y_next_after_prev store1 x y hx1 hy1).trans (y_next_after_set store x y hx hy)
  let updated := store.set x.val (some { (store.get x).get hx with
    next := ((store.get y).get hy).next, prev := some y }) x.isLt
  have hS2 : store2 = updated := first_two_store store x y hx hy
  let linked := match oldY.next with
    | none => updated
    | some z => updated.set z.val
        ((updated.get z).map fun (node : Node α (Fin n)) => { node with prev := some x })
        z.isLt
  change (listInsert store x y hx hy hs).ret = linked.set y.val
    ((linked.get y).map fun (node : Node α (Fin n)) => { node with next := some x }) y.isLt
  simp only [listInsert, TimeM.ret_bind]
  split
  · rename_i he
    change currentY2.next = none at he
    have hOld : oldY.next = none := hp.symm.trans he
    have hLinked : linked = updated := by simp only [linked, hOld]
    rw [hLinked]
    simp only [TimeM.ret_bind, TimeM.ret_pure]
    change store2.set y.val (some { currentY2 with next := some x }) y.isLt =
      updated.set y.val ((updated.get y).map fun (node : Node α (Fin n)) =>
        { node with next := some x }) y.isLt
    calc
      _ = store2.set y.val ((store2.get y).map fun (node : Node α (Fin n)) =>
          { node with next := some x }) y.isLt :=
        set_map_get store2 y hy2 (fun node => { node with next := some x })
      _ = _ := by rw [hS2]
  · rename_i z he
    change currentY2.next = some z at he
    have hOld : oldY.next = some z := hp.symm.trans he
    have hz := hs z hOld
    have hz1 := (allocated_set store x hx nextX z).trans hz
    have hz2 := (allocated_set store1 x hx1 prevX z).trans hz1
    let currentZ := (store2.get z).get hz2
    let newZ := { currentZ with prev := some x }
    let store3 := store2.set z.val (some newZ) z.isLt
    have hy3 := (allocated_set store2 z hz2 newZ y).trans hy2
    let currentY3 := (store3.get y).get hy3
    let backlinked := updated.set z.val
      ((updated.get z).map fun (node : Node α (Fin n)) => { node with prev := some x }) z.isLt
    have hS3 : store3 = backlinked := by
      calc
        _ = store2.set z.val ((store2.get z).map fun (node : Node α (Fin n)) =>
            { node with prev := some x }) z.isLt :=
          set_map_get store2 z hz2 (fun node => { node with prev := some x })
        _ = _ := by rw [hS2]
    have hLinked : linked = backlinked := by
      simp only [linked, hOld]
      rfl
    rw [hLinked]
    simp only [TimeM.ret_bind, TimeM.ret_pure]
    change store3.set y.val (some { currentY3 with next := some x }) y.isLt =
      backlinked.set y.val ((backlinked.get y).map fun (node : Node α (Fin n)) =>
        { node with next := some x }) y.isLt
    calc
      _ = store3.set y.val ((store3.get y).map fun (node : Node α (Fin n)) =>
          { node with next := some x }) y.isLt :=
        set_map_get store3 y hy3 (fun node => { node with next := some x })
      _ = _ := by rw [hS3]

/-- The whole-store characteristic reduced at one index, preserving all aliases. -/
public theorem listInsert_get {α : Type u} {n : Nat}
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
  rw [listInsert_ret]
  cases he : ((store.get y).get hy).next with
  | none =>
    by_cases hyz : y = z <;> simp_all [get_set]
  | some w =>
    by_cases hyz : y = z <;> by_cases hwz : w = z <;>
      subst_vars <;> simp_all [get_set]

/-- Cells outside the three source write targets are unchanged. -/
public theorem listInsert_frame {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome)
    (hxz : x ≠ z) (hyz : y ≠ z) (hsz : ((store.get y).get hy).next ≠ some z) :
    (listInsert store x y hx hy hs).ret.get z = store.get z := by
  rw [listInsert_get]
  simp [hxz, hyz, hsz]

/-- Allocation is preserved at every cell, including overlapping write targets. -/
public theorem listInsert_allocated {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    ((listInsert store x y hx hy hs).ret.get z).isSome =
      (store.get z).isSome := by
  rw [listInsert_get]
  by_cases hxz : x = z
  · subst z
    split_ifs <;> simp_all
  · split_ifs <;> simp_all

/-- Full payloads are preserved at every cell; no payload equality is required. -/
public theorem listInsert_payload {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    ((listInsert store x y hx hy hs).ret.get z).map Node.payload =
      (store.get z).map Node.payload := by
  rw [listInsert_get]
  by_cases hxz : x = z
  · subst z
    have hp : (store.get x).map Node.payload = some ((store.get x).get hx).payload :=
      (congrArg (Option.map Node.payload) (Option.some_get hx)).symm
    simp only [ite_true]
    split_ifs <;> simp only [Option.map_some] <;> exact hp.symm
  · split_ifs <;> simp_all <;> rfl

private lemma inserted_nodup {α : Type u} (ids : List α) (x : α) (i : Nat)
    (hi : i ≤ ids.length) (nd : ids.Nodup) (fresh : x ∉ ids) :
    (ids.insertIdx i x).Nodup :=
  (List.perm_insertIdx x ids hi).symm.nodup (List.nodup_cons.mpr ⟨fresh, nd⟩)

private lemma inserted_head {α : Type u} (ids : List α) (x : α) (k : Nat) :
    (ids.insertIdx (k + 1) x).head? = ids.head? := by
  cases ids <;> rfl

private lemma represented_next {α : Type u} {n : Nat}
    {store : Vector (Option (Node α (Fin n))) n} {head : Option (Fin n)}
    {ids : List (Fin n)} (rep : Represents store head ids)
    (k : Nat) (hk : k < ids.length) (hy : (store.get ids[k]).isSome) :
    ((store.get ids[k]).get hy).next = ids[k + 1]? := by
  obtain ⟨node, hn, _, hnext⟩ := rep.2.2 k hk
  simpa [hn] using hnext

private lemma successor_ne_fresh {α : Type u} (ids : List α)
    (x : α) (fresh : x ∉ ids) (k : Nat) : ids[k + 1]? ≠ some x := by
  intro he
  obtain ⟨hs, hget⟩ := List.getElem?_eq_some_iff.mp he
  exact fresh (hget ▸ List.getElem_mem hs)

private lemma inserted_cell {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome)
    (hxy : x ≠ y) (hsx : ((store.get y).get hy).next ≠ some x) :
    (listInsert store x y hx hy hs).ret.get x =
      some { (store.get x).get hx with
        next := ((store.get y).get hy).next, prev := some y } := by
  have hyx : y ≠ x := fun he => hxy he.symm
  rw [listInsert_get]
  simp [hyx, hsx]

private lemma old_cell {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x : Fin n)
    {head : Option (Fin n)} {ids : List (Fin n)} (rep : Represents store head ids)
    (fresh : x ∉ ids) (k : Nat) (hk : k < ids.length)
    (hx : (store.get x).isSome) (hy : (store.get ids[k]).isSome)
    (hs : ∀ z, ((store.get ids[k]).get hy).next = some z → (store.get z).isSome)
    (i : Nat) (hi : i < ids.length) (node : Node α (Fin n))
    (hn : store.get ids[i] = some node) :
    (listInsert store x ids[k] hx hy hs).ret.get ids[i] =
      some { node with
        prev := if i = k + 1 then some x else node.prev
        next := if i = k then some x else node.next } := by
  have hxne : x ≠ ids[i] := fun he => fresh (he ▸ List.getElem_mem hi)
  have hyiff : ids[k] = ids[i] ↔ i = k := by
    rw [rep.1.getElem_inj_iff]
    exact eq_comm
  have hsiff : ids[k + 1]? = some ids[i] ↔ i = k + 1 := by
    constructor
    · intro he
      obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp he
      exact (rep.1.getElem_inj_iff.mp hget).symm
    · intro he
      subst i
      exact List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
  rw [listInsert_get, represented_next rep k hk hy]
  simp only [hxne, ite_false, hn, hyiff, hsiff]
  by_cases his : i = k + 1 <;> by_cases hiy : i = k <;>
    simp [his, hiy]

private lemma prefix_links {α : Type u} (ids : List α) (x : α) (k i : Nat)
    (hik : i ≤ k) (hk : k < ids.length) (prev next : Option α)
    (hp : prev = if i = 0 then none else ids[i - 1]?) (hn : next = ids[i + 1]?) :
    prev = (if i = 0 then none else (ids.insertIdx (k + 1) x)[i - 1]?) ∧
      (if i = k then some x else next) = (ids.insertIdx (k + 1) x)[i + 1]? := by
  constructor
  · rw [hp]
    by_cases hi : i = 0
    · simp [hi]
    · rw [List.getElem?_insertIdx_of_lt (by omega)]
  · by_cases hi : i = k
    · subst i
      simp [List.getElem?_insertIdx_self, show k + 1 ≤ ids.length by omega]
    · rw [ite_eq_right hi, hn, List.getElem?_insertIdx_of_lt (by omega)]

private lemma suffix_links {α : Type u} (ids : List α) (x : α) (k j : Nat)
    (hkj : k < j) (hk : k < ids.length) (prev next : Option α)
    (hp : prev = if j = 0 then none else ids[j - 1]?) (hn : next = ids[j + 1]?) :
    (if j = k + 1 then some x else prev) =
        (if j + 1 = 0 then none else (ids.insertIdx (k + 1) x)[j + 1 - 1]?) ∧
      next = (ids.insertIdx (k + 1) x)[j + 1 + 1]? := by
  have hj0 : j ≠ 0 := by omega
  simp only [show j + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
  constructor
  · by_cases hj : j = k + 1
    · subst j
      simp [List.getElem?_insertIdx_self, show k + 1 ≤ ids.length by omega]
    · rw [ite_eq_right hj, hp, ite_eq_right hj0,
        List.getElem?_insertIdx_of_gt (by omega)]
  · rw [hn, List.getElem?_insertIdx_of_gt (by omega)]
    congr 1

private lemma prefix_node {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x : Fin n)
    {head : Option (Fin n)} {ids : List (Fin n)} (rep : Represents store head ids)
    (fresh : x ∉ ids) (k : Nat) (hk : k < ids.length)
    (hx : (store.get x).isSome) (hy : (store.get ids[k]).isSome)
    (hs : ∀ z, ((store.get ids[k]).get hy).next = some z → (store.get z).isSome)
    (i : Nat) (hik : i ≤ k) (hi : i < (ids.insertIdx (k + 1) x).length) :
    ∃ node, (listInsert store x ids[k] hx hy hs).ret.get
        (ids.insertIdx (k + 1) x)[i] = some node ∧
      node.prev = (if i = 0 then none else (ids.insertIdx (k + 1) x)[i - 1]?) ∧
      node.next = (ids.insertIdx (k + 1) x)[i + 1]? := by
  have hio : i < ids.length := by omega
  rw [List.getElem_insertIdx_of_lt (by omega) hi]
  obtain ⟨node, hn, hp, ht⟩ := rep.2.2 i hio
  obtain ⟨hpnew, htnew⟩ := prefix_links ids x k i hik hk node.prev node.next hp ht
  refine ⟨{ node with next := if i = k then some x else node.next }, ?_, hpnew, htnew⟩
  simpa [show i ≠ k + 1 by omega] using old_cell store x rep fresh k hk hx hy hs i hio node hn

private lemma suffix_node {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x : Fin n)
    {head : Option (Fin n)} {ids : List (Fin n)} (rep : Represents store head ids)
    (fresh : x ∉ ids) (k : Nat) (hk : k < ids.length)
    (hx : (store.get x).isSome) (hy : (store.get ids[k]).isSome)
    (hs : ∀ z, ((store.get ids[k]).get hy).next = some z → (store.get z).isSome)
    (i : Nat) (hki : k + 1 < i) (hi : i < (ids.insertIdx (k + 1) x).length) :
    ∃ node, (listInsert store x ids[k] hx hy hs).ret.get
        (ids.insertIdx (k + 1) x)[i] = some node ∧
      node.prev = (if i = 0 then none else (ids.insertIdx (k + 1) x)[i - 1]?) ∧
      node.next = (ids.insertIdx (k + 1) x)[i + 1]? := by
  have hlen := List.length_insertIdx_of_le_length (show k + 1 ≤ ids.length by omega) x
  have hio : i - 1 < ids.length := by omega
  rw [List.getElem_insertIdx_of_gt hki hi]
  obtain ⟨node, hn, hp, ht⟩ := rep.2.2 (i - 1) hio
  obtain ⟨hpnew, htnew⟩ := suffix_links ids x k (i - 1) (by omega) hk
    node.prev node.next hp ht
  have hind : i - 1 + 1 = i := by omega
  rw [hind] at hpnew htnew
  refine ⟨{ node with prev := if i - 1 = k + 1 then some x else node.prev },
    ?_, hpnew, htnew⟩
  simpa [show i - 1 ≠ k by omega] using
    old_cell store x rep fresh k hk hx hy hs (i - 1) hio node hn

private lemma inserted_node {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x : Fin n)
    {head : Option (Fin n)} {ids : List (Fin n)} (rep : Represents store head ids)
    (fresh : x ∉ ids) (k : Nat) (hk : k < ids.length)
    (hx : (store.get x).isSome) (hy : (store.get ids[k]).isSome)
    (hs : ∀ z, ((store.get ids[k]).get hy).next = some z → (store.get z).isSome)
    (hi : k + 1 < (ids.insertIdx (k + 1) x).length) :
    ∃ node, (listInsert store x ids[k] hx hy hs).ret.get
        (ids.insertIdx (k + 1) x)[k + 1] = some node ∧
      node.prev = (if k + 1 = 0 then none else (ids.insertIdx (k + 1) x)[k + 1 - 1]?) ∧
      node.next = (ids.insertIdx (k + 1) x)[k + 1 + 1]? := by
  rw [List.getElem_insertIdx_self hi]
  have hxy : x ≠ ids[k] := fun he => fresh (he ▸ List.getElem_mem hk)
  have hsx : ((store.get ids[k]).get hy).next ≠ some x := by
    rw [represented_next rep k hk hy]
    exact successor_ne_fresh ids x fresh k
  refine ⟨{ (store.get x).get hx with
    next := ((store.get ids[k]).get hy).next
    prev := some ids[k] }, inserted_cell store x ids[k] hx hy hs hxy hsx, ?_, ?_⟩
  · simp only [show k + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
    rw [List.getElem?_insertIdx_of_lt (by omega)]
    exact (List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩).symm
  · rw [List.getElem?_insertIdx_of_gt (by omega)]
    simpa using represented_next rep k hk hy

/-- Inserting an allocated fresh node after index `k` preserves the exact source-list
representation, with no head write. Freshness is a proof premise, not an execution guard. -/
public theorem listInsert_represents {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x : Fin n)
    (head : Option (Fin n)) (ids : List (Fin n)) (rep : Represents store head ids)
    (fresh : x ∉ ids) (k : Nat) (hk : k < ids.length)
    (hx : (store.get x).isSome) (hy : (store.get ids[k]).isSome)
    (hs : ∀ z, ((store.get ids[k]).get hy).next = some z → (store.get z).isSome) :
    Represents (listInsert store x ids[k] hx hy hs).ret head
      (ids.insertIdx (k + 1) x) := by
  refine ⟨inserted_nodup ids x (k + 1) (by omega) rep.1 fresh,
    rep.2.1.trans (inserted_head ids x k).symm, ?_⟩
  intro i hi
  by_cases hik : i ≤ k
  · exact prefix_node store x rep fresh k hk hx hy hs i hik hi
  · by_cases hie : i = k + 1
    · subst i
      exact inserted_node store x rep fresh k hk hx hy hs hi
    · exact suffix_node store x rep fresh k hk hx hy hs i (by omega) hi

/-- Insertion preserves another represented list whose identities are disjoint from
the original list and do not contain the fresh insertion identity. -/
public theorem listInsert_disjoint_represents {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x : Fin n)
    (head otherHead : Option (Fin n)) (ids otherIds : List (Fin n))
    (rep : Represents store head ids) (otherRep : Represents store otherHead otherIds)
    (disjoint : List.Disjoint ids otherIds) (freshOther : x ∉ otherIds)
    (k : Nat) (hk : k < ids.length) (hx : (store.get x).isSome)
    (hy : (store.get ids[k]).isSome)
    (hs : ∀ z, ((store.get ids[k]).get hy).next = some z → (store.get z).isSome) :
    Represents (listInsert store x ids[k] hx hy hs).ret otherHead otherIds := by
  refine ⟨otherRep.1, otherRep.2.1, ?_⟩
  intro i hi
  obtain ⟨node, hn, hp, ht⟩ := otherRep.2.2 i hi
  have hm : otherIds[i] ∈ otherIds := List.getElem_mem hi
  have hxne : x ≠ otherIds[i] := fun he => freshOther (he ▸ hm)
  have hyne : ids[k] ≠ otherIds[i] := fun he => disjoint (List.getElem_mem hk) (he ▸ hm)
  have hsne : ((store.get ids[k]).get hy).next ≠ some otherIds[i] := by
    rw [represented_next rep k hk hy]
    intro he
    obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp he
    exact disjoint (hget ▸ List.getElem_mem hj) hm
  refine ⟨node, ?_, hp, ht⟩
  rw [listInsert_frame store x ids[k] otherIds[i] hx hy hs hxne hyne hsne]
  exact hn

end Cslib.Algorithms.Lean.DoublyLinkedList
