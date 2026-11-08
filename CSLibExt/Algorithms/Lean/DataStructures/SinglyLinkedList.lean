/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Init.Data.Vector.Lemmas
public import Mathlib.Data.List.Nodup

import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Find
import Mathlib.Data.List.InsertIdx

/-!
# Singly-linked lists over a node pool

A `Node` has a payload and an optional next pointer; `none` denotes NIL.
As in `DoublyLinkedList.Basic`, an allocated node pool is a
`Vector (Option (Node α (Fin capacity))) capacity`, and `Represents` relates a
pool and a header to an ordered list of distinct node identities, here with
next pointers only.

The operations are plain functions on the pool (no cost model): `prepend`
links an already allocated node at the head, `insertAfter` links an allocated
node after a given node, `deleteHead` drops the head, and `deleteAfter`
splices out the successor of a given node. Each operation comes with a
pointwise store equation and a `Represents` correctness theorem describing how
the represented identity list changes. `contents` collects the payloads stored
at a list of identities, and `search` follows next pointers with an explicit
fuel bound (the public wrapper uses the pool capacity), returning the first
identity whose payload equals the target.

Freshness of a linked-in node is a premise of the representation proofs, not
an execution guard, matching the doubly-linked list development.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SinglyLinkedList

universe u v

/-- A node payload with a next identity; `none` denotes NIL. -/
structure Node (α : Type u) (ι : Type v) where
  /-- The full payload, including any key and satellite data. -/
  payload : α
  /-- Next node identity, or NIL at the tail. -/
  next : Option ι
deriving DecidableEq, Repr

/-- An allocated singly-linked list with exactly the distinct identities `ids`. -/
def Represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity)) : Prop :=
  ids.Nodup ∧ head = ids.head? ∧
    ∀ (i : Nat) (hi : i < ids.length), ∃ node,
      store.get ids[i] = some node ∧
      node.next = ids[i + 1]?

/-- The empty identity list is represented by any pool with header NIL. -/
theorem represents_nil {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) :
    Represents store none ([] : List (Fin capacity)) := by
  refine ⟨List.nodup_nil, rfl, ?_⟩
  intro i hi
  simp at hi

/-- Every represented identity is allocated. -/
theorem represents_allocated {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) {i : Fin capacity} (hi : i ∈ ids) :
    (store.get i).isSome := by
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem hi
  obtain ⟨node, hn, -⟩ := rep.2.2 k hk
  rw [← he, hn]
  rfl

/-- The stored next pointer at position `k` is the following identity. -/
private lemma represented_next {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) :
    ((store.get ids[k]).get hy).next = ids[k + 1]? := by
  obtain ⟨node, hn, hnext⟩ := rep.2.2 k hk
  simpa only [hn, Option.get_some] using hnext

/-- A represented nonempty list splits into its head node and a represented tail. -/
private lemma represents_cons {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {a : Fin capacity} {rest : List (Fin capacity)}
    (rep : Represents store head (a :: rest)) :
    ∃ node, store.get a = some node ∧ Represents store node.next rest := by
  obtain ⟨node, hn, hnext⟩ := rep.2.2 0 (by simp)
  have hn' : store.get a = some node := by simpa using hn
  refine ⟨node, hn', (List.nodup_cons.mp rep.1).2, ?_, ?_⟩
  · simpa only [List.getElem?_cons_succ, List.head?_eq_getElem?] using hnext
  · intro i hi
    have hii : i + 1 < (a :: rest).length := by
      rw [List.length_cons]; omega
    obtain ⟨node₂, hn₂, hnext₂⟩ := rep.2.2 (i + 1) hii
    refine ⟨node₂, by simpa only [List.getElem_cons_succ] using hn₂,
      by simpa only [List.getElem?_cons_succ] using hnext₂⟩

private lemma vector_get_set {α : Type u} {n : Nat}
    (xs : Vector α n) (i j : Fin n) (a : α) :
    (xs.set i.val a i.isLt).get j = if i = j then a else xs.get j := by
  change (xs.set i.val a i.isLt)[j.val] = if i = j then a else xs[j.val]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff]

private lemma map_insertIdx {α β : Type*} (f : α → β) (l : List α) (i : Nat) (a : α) :
    (l.insertIdx i a).map f = (l.map f).insertIdx i (f a) := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons b t ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (List.cons (f b)) (ih (i := i))

private lemma map_eraseIdx {α β : Type*} (f : α → β) (l : List α) (i : Nat) :
    (l.eraseIdx i).map f = (l.map f).eraseIdx i := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons b t ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (List.cons (f b)) (ih (i := i))

/-- Payloads stored at `ids`, in order; `none` marks an unallocated cell. -/
def contents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (ids : List (Fin capacity)) : List (Option α) :=
  ids.map fun i => (store.get i).map Node.payload

/-- Contents have one entry per identity. -/
@[simp]
theorem contents_length {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (ids : List (Fin capacity)) :
    (contents store ids).length = ids.length :=
  List.length_map _

/-- Contents depend only on the cells at the listed identities. -/
theorem contents_congr {α : Type u} {capacity : Nat}
    {store store' : Vector (Option (Node α (Fin capacity))) capacity}
    {ids : List (Fin capacity)}
    (h : ∀ i ∈ ids, store'.get i = store.get i) :
    contents store' ids = contents store ids := by
  unfold contents
  exact List.map_congr_left fun i hi => by rw [h i hi]

/-- In a represented list every content entry is present. -/
theorem represents_contents_isSome {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) :
    ∀ x ∈ contents store ids, x.isSome = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [Option.isSome_map]
  exact represents_allocated rep hi

/-- Prepend an already allocated node: point it at the old head and make it the head. -/
def prepend {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome) :
    Vector (Option (Node α (Fin capacity))) capacity × Option (Fin capacity) :=
  (store.set x.val (some { (store.get x).get hx with next := head }) x.isLt, some x)

/-- The prepended node is always the new head. -/
theorem prepend_head {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome) :
    (prepend store head x hx).2 = some x :=
  rfl

/-- Pointwise effect of prepending: only the cell at `x` changes. -/
theorem prepend_get {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome) (z : Fin capacity) :
    (prepend store head x hx).1.get z =
      if x = z then some { (store.get x).get hx with next := head } else store.get z := by
  exact vector_get_set store x z _

/-- Cells other than the prepended node are unchanged. -/
theorem prepend_frame {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome) (z : Fin capacity) (hz : x ≠ z) :
    (prepend store head x hx).1.get z = store.get z := by
  rw [prepend_get, ite_eq_right hz]

/-- The prepended cell keeps its payload and points at the old head. -/
theorem prepend_node {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome) :
    (prepend store head x hx).1.get x =
      some { (store.get x).get hx with next := head } := by
  rw [prepend_get, ite_eq_left rfl]

/-- Prepending a fresh allocated identity conses it onto the represented list. -/
theorem prepend_represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (ids : List (Fin capacity)) (rep : Represents store head ids) (fresh : x ∉ ids) :
    Represents (prepend store head x hx).1 (prepend store head x hx).2 (x :: ids) := by
  rw [prepend_head]
  refine ⟨List.nodup_cons.mpr ⟨fresh, rep.1⟩, rfl, ?_⟩
  intro i hi
  cases i with
  | zero =>
    refine ⟨{ (store.get x).get hx with next := head }, ?_, ?_⟩
    · simpa using prepend_node store head x hx
    · show head = ids[0]?
      rw [← List.head?_eq_getElem?]
      exact rep.2.1
  | succ j =>
    have hj : j < ids.length := by
      rw [List.length_cons] at hi
      omega
    obtain ⟨node, hn, hnext⟩ := rep.2.2 j hj
    have xj : x ≠ ids[j] := fun he => fresh (he ▸ List.getElem_mem hj)
    refine ⟨node, ?_, ?_⟩
    · have hcell := (prepend_frame store head x hx ids[j] xj).trans hn
      simpa using hcell
    · simpa using hnext

/-- Prepending conses the new payload onto the contents. -/
theorem prepend_contents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (ids : List (Fin capacity)) (fresh : x ∉ ids) :
    contents (prepend store head x hx).1 (x :: ids) =
      some ((store.get x).get hx).payload :: contents store ids := by
  have htail : contents (prepend store head x hx).1 ids = contents store ids :=
    contents_congr fun i hi =>
      prepend_frame store head x hx i (fun he => fresh (he ▸ hi))
  show ((prepend store head x hx).1.get x).map Node.payload ::
      contents (prepend store head x hx).1 ids = _
  rw [prepend_node, htail]
  rfl

/-- Insert an already allocated node `x` after the allocated node `y`. -/
def insertAfter {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y x : Fin capacity)
    (hy : (store.get y).isSome) (hx : (store.get x).isSome) :
    Vector (Option (Node α (Fin capacity))) capacity :=
  let store₁ := store.set x.val
    (some { (store.get x).get hx with next := ((store.get y).get hy).next }) x.isLt
  store₁.set y.val ((store₁.get y).map fun node => { node with next := some x }) y.isLt

/-- Pointwise effect of insertion: `x` is written first, then `y` is relinked. -/
theorem insertAfter_get {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y x : Fin capacity)
    (hy : (store.get y).isSome) (hx : (store.get x).isSome) (z : Fin capacity) :
    (insertAfter store y x hy hx).get z =
      if y = z then
        (if x = z then
          some { (store.get x).get hx with next := ((store.get y).get hy).next }
        else store.get z).map (fun node => { node with next := some x })
      else if x = z then
        some { (store.get x).get hx with next := ((store.get y).get hy).next }
      else store.get z := by
  by_cases hyz : y = z <;> by_cases hxz : x = z <;>
    subst_vars <;> simp_all [insertAfter, vector_get_set]

/-- Cells other than the inserted node and its predecessor are unchanged. -/
theorem insertAfter_frame {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y x : Fin capacity)
    (hy : (store.get y).isSome) (hx : (store.get x).isSome) (z : Fin capacity)
    (hyz : y ≠ z) (hxz : x ≠ z) :
    (insertAfter store y x hy hx).get z = store.get z := by
  rw [insertAfter_get, ite_eq_right hyz, ite_eq_right hxz]

/-- Insertion preserves every payload. -/
theorem insertAfter_payload {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y x : Fin capacity)
    (hy : (store.get y).isSome) (hx : (store.get x).isSome) (z : Fin capacity) :
    ((insertAfter store y x hy hx).get z).map Node.payload =
      (store.get z).map Node.payload := by
  rw [insertAfter_get]
  by_cases hxz : x = z
  · subst z
    have hp : (store.get x).map Node.payload =
        some ((store.get x).get hx).payload :=
      (congrArg (Option.map Node.payload) (Option.some_get hx)).symm
    by_cases hyx : y = x <;> simp [hyx, hp]
  · by_cases hyz : y = z <;> simp [hyz, hxz, Option.map_map, Function.comp_def]

private lemma insertIdx_succ_head? {α : Type*} (l : List α) (a : α) (k : Nat) :
    (l.insertIdx (k + 1) a).head? = l.head? := by
  cases l <;> rfl

/-- After insertion, an old cell changes only at the predecessor position. -/
private lemma insertAfter_old_cell {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) (fresh : x ∉ ids)
    (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) (hx : (store.get x).isSome)
    (i : Nat) (hi : i < ids.length) (node : Node α (Fin capacity))
    (hn : store.get ids[i] = some node) :
    (insertAfter store ids[k] x hy hx).get ids[i] =
      some { node with next := if i = k then some x else node.next } := by
  have hxne : x ≠ ids[i] := fun he => fresh (he ▸ List.getElem_mem hi)
  have hyiff : ids[k] = ids[i] ↔ i = k := by
    rw [rep.1.getElem_inj_iff]
    exact eq_comm
  rw [insertAfter_get]
  simp only [hxne, ite_false, hn, hyiff, Option.map_some]
  by_cases hik : i = k <;> simp [hik]

/-- The inserted cell keeps its payload and inherits the predecessor's old successor. -/
private lemma insertAfter_new_cell {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) (fresh : x ∉ ids)
    (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) (hx : (store.get x).isSome) :
    (insertAfter store ids[k] x hy hx).get x =
      some { (store.get x).get hx with next := ids[k + 1]? } := by
  have hyx : ids[k] ≠ x := fun he => fresh (he ▸ List.getElem_mem hk)
  rw [insertAfter_get, ite_eq_right hyx, ite_eq_left rfl,
    represented_next rep k hk hy]

private lemma insertAfter_prefix {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) (fresh : x ∉ ids)
    (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) (hx : (store.get x).isSome)
    (i : Nat) (hik : i ≤ k) (hi : i < (ids.insertIdx (k + 1) x).length) :
    ∃ node, (insertAfter store ids[k] x hy hx).get (ids.insertIdx (k + 1) x)[i] =
        some node ∧
      node.next = (ids.insertIdx (k + 1) x)[i + 1]? := by
  have hio : i < ids.length := by omega
  rw [List.getElem_insertIdx_of_lt (by omega) hi]
  obtain ⟨node, hn, hnext⟩ := rep.2.2 i hio
  refine ⟨{ node with next := if i = k then some x else node.next },
    insertAfter_old_cell store x rep fresh k hk hy hx i hio node hn, ?_⟩
  by_cases hik' : i = k
  · subst i
    simp [List.getElem?_insertIdx_self, show k + 1 ≤ ids.length by omega]
  · simp only [ite_eq_right hik']
    rw [hnext, List.getElem?_insertIdx_of_lt (by omega)]

private lemma insertAfter_inserted {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) (fresh : x ∉ ids)
    (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) (hx : (store.get x).isSome)
    (hi : k + 1 < (ids.insertIdx (k + 1) x).length) :
    ∃ node, (insertAfter store ids[k] x hy hx).get (ids.insertIdx (k + 1) x)[k + 1] =
        some node ∧
      node.next = (ids.insertIdx (k + 1) x)[k + 1 + 1]? := by
  rw [List.getElem_insertIdx_self hi]
  refine ⟨{ (store.get x).get hx with next := ids[k + 1]? },
    insertAfter_new_cell store x rep fresh k hk hy hx, ?_⟩
  rw [List.getElem?_insertIdx_of_gt (by omega)]
  simp

private lemma insertAfter_suffix {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) (fresh : x ∉ ids)
    (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) (hx : (store.get x).isSome)
    (i : Nat) (hki : k + 1 < i) (hi : i < (ids.insertIdx (k + 1) x).length) :
    ∃ node, (insertAfter store ids[k] x hy hx).get (ids.insertIdx (k + 1) x)[i] =
        some node ∧
      node.next = (ids.insertIdx (k + 1) x)[i + 1]? := by
  have hlen := List.length_insertIdx_of_le_length (show k + 1 ≤ ids.length by omega) x
  have hio : i - 1 < ids.length := by omega
  rw [List.getElem_insertIdx_of_gt hki hi]
  obtain ⟨node, hn, hnext⟩ := rep.2.2 (i - 1) hio
  refine ⟨{ node with next := if i - 1 = k then some x else node.next },
    insertAfter_old_cell store x rep fresh k hk hy hx (i - 1) hio node hn, ?_⟩
  simp only [ite_eq_right (show i - 1 ≠ k by omega)]
  rw [hnext, List.getElem?_insertIdx_of_gt (by omega)]
  simp only [show i - 1 + 1 = i by omega, show i + 1 - 1 = i by omega]

/-- Inserting a fresh allocated node after position `k` inserts its identity at
position `k + 1` of the represented list; the header is unchanged. -/
theorem insertAfter_represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity))
    (rep : Represents store head ids) (fresh : x ∉ ids)
    (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) (hx : (store.get x).isSome) :
    Represents (insertAfter store ids[k] x hy hx) head (ids.insertIdx (k + 1) x) := by
  refine ⟨(List.perm_insertIdx x ids (by omega)).symm.nodup
      (List.nodup_cons.mpr ⟨fresh, rep.1⟩),
    rep.2.1.trans (insertIdx_succ_head? ids x k).symm, ?_⟩
  intro i hi
  by_cases hik : i ≤ k
  · exact insertAfter_prefix store x rep fresh k hk hy hx i hik hi
  · by_cases hie : i = k + 1
    · subst i
      exact insertAfter_inserted store x rep fresh k hk hy hx hi
    · exact insertAfter_suffix store x rep fresh k hk hy hx i (by omega) hi

/-- Insertion inserts the new payload at the same position of the contents. -/
theorem insertAfter_contents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    (ids : List (Fin capacity)) (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) (hx : (store.get x).isSome) :
    contents (insertAfter store ids[k] x hy hx) (ids.insertIdx (k + 1) x) =
      (contents store ids).insertIdx (k + 1) (some ((store.get x).get hx).payload) := by
  have hmap : contents (insertAfter store ids[k] x hy hx) (ids.insertIdx (k + 1) x) =
      (ids.insertIdx (k + 1) x).map (fun i => (store.get i).map Node.payload) :=
    List.map_congr_left fun i _ => insertAfter_payload store ids[k] x hy hx i
  have hpayload : (store.get x).map Node.payload =
      some ((store.get x).get hx).payload :=
    (congrArg (Option.map Node.payload) (Option.some_get hx)).symm
  show contents (insertAfter store ids[k] x hy hx) (ids.insertIdx (k + 1) x) = _
  rw [hmap]
  show (ids.insertIdx (k + 1) x).map (fun i => (store.get i).map Node.payload) =
    (contents store ids).insertIdx (k + 1) (some ((store.get x).get hx).payload)
  rw [map_insertIdx]
  show (ids.map (fun i => (store.get i).map Node.payload)).insertIdx (k + 1)
      ((store.get x).map Node.payload) = _
  rw [hpayload]
  rfl

/-- Delete the head node: the pool is unchanged and the header follows its next pointer. -/
def deleteHead {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) :
    Vector (Option (Node α (Fin capacity))) capacity × Option (Fin capacity) :=
  (store, head.bind fun h => (store.get h).bind fun node => node.next)

/-- Deleting the head drops the first represented identity. -/
theorem deleteHead_represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity))
    (rep : Represents store head ids) :
    Represents (deleteHead store head).1 (deleteHead store head).2 ids.tail := by
  cases ids with
  | nil =>
    have hhead : head = none := rep.2.1
    subst head
    exact represents_nil store
  | cons a rest =>
    obtain ⟨node, hn, htail⟩ := represents_cons rep
    have hhead : (deleteHead store head).2 = node.next := by
      have hh : head = some a := rep.2.1
      show head.bind (fun h => (store.get h).bind fun node => node.next) = node.next
      rw [hh]
      simp only [Option.bind_some, hn, Option.bind_some]
    show Represents store (deleteHead store head).2 rest
    rw [hhead]
    exact htail

/-- Delete the successor of the allocated node `y` by splicing `y` past it.
The removed node stays allocated; at the tail this is a no-op on links. -/
def deleteAfter {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y : Fin capacity) (hy : (store.get y).isSome) :
    Vector (Option (Node α (Fin capacity))) capacity :=
  store.set y.val (some { (store.get y).get hy with
    next := ((store.get y).get hy).next.bind
      fun n => (store.get n).bind fun node => node.next }) y.isLt

/-- Pointwise effect of deleting a successor: only the cell at `y` changes. -/
theorem deleteAfter_get {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y : Fin capacity) (hy : (store.get y).isSome) (z : Fin capacity) :
    (deleteAfter store y hy).get z =
      if y = z then
        some { (store.get y).get hy with
          next := ((store.get y).get hy).next.bind
            fun n => (store.get n).bind fun node => node.next }
      else store.get z := by
  exact vector_get_set store y z _

/-- Cells other than the predecessor of the deleted node are unchanged. -/
theorem deleteAfter_frame {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y : Fin capacity) (hy : (store.get y).isSome) (z : Fin capacity)
    (hyz : y ≠ z) :
    (deleteAfter store y hy).get z = store.get z := by
  rw [deleteAfter_get, ite_eq_right hyz]

/-- Deleting a successor preserves every payload. -/
theorem deleteAfter_payload {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y : Fin capacity) (hy : (store.get y).isSome) (z : Fin capacity) :
    ((deleteAfter store y hy).get z).map Node.payload =
      (store.get z).map Node.payload := by
  rw [deleteAfter_get]
  by_cases hyz : y = z
  · subst z
    have hp : (store.get y).map Node.payload =
        some ((store.get y).get hy).payload :=
      (congrArg (Option.map Node.payload) (Option.some_get hy)).symm
    simp [hp]
  · rw [ite_eq_right hyz]

private lemma eraseIdx_succ_head? {α : Type*} (l : List α) (k : Nat) :
    (l.eraseIdx (k + 1)).head? = l.head? := by
  cases l <;> rfl

/-- In a represented list, the splice target is the identity two positions on. -/
private lemma deleteAfter_next_eq {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity))
    (rep : Represents store head ids) (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) :
    (((store.get ids[k]).get hy).next.bind
      fun n => (store.get n).bind fun node => node.next) = ids[k + 1 + 1]? := by
  by_cases h2 : k + 1 < ids.length
  · obtain ⟨node₂, hn₂, hnext₂⟩ := rep.2.2 (k + 1) h2
    rw [represented_next rep k hk hy, List.getElem?_eq_getElem h2,
      Option.bind_some, hn₂, Option.bind_some]
    exact hnext₂
  · have hnext : ((store.get ids[k]).get hy).next = none := by
      rw [represented_next rep k hk hy]
      exact List.getElem?_eq_none (by omega)
    rw [hnext]
    simp only [Option.bind_none]
    exact (List.getElem?_eq_none (show ids.length ≤ k + 1 + 1 by omega)).symm

/-- After splicing, an old cell changes only at the predecessor position. -/
private lemma deleteAfter_old_cell {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome)
    (j : Nat) (hj : j < ids.length) (node : Node α (Fin capacity))
    (hn : store.get ids[j] = some node) :
    (deleteAfter store ids[k] hy).get ids[j] =
      some { node with next := if j = k then ids[k + 1 + 1]? else node.next } := by
  by_cases hjk : j = k
  · subst j
    have hnode : (store.get ids[k]).get hy = node :=
      Option.some.inj ((Option.some_get hy).trans hn)
    have hbind := deleteAfter_next_eq store head ids rep k hk hy
    rw [deleteAfter_get, hbind, hnode]
    split_ifs <;> simp_all
  · have hne : ids[k] ≠ ids[j] :=
      fun he => hjk (rep.1.getElem_inj_iff.mp he).symm
    simp [deleteAfter_frame store ids[k] hy ids[j] hne, hn, hjk]

/-- Deleting the successor of position `k` erases position `k + 1` of the
represented list (a no-op at the tail); the header is unchanged. -/
theorem deleteAfter_represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity))
    (rep : Represents store head ids) (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) :
    Represents (deleteAfter store ids[k] hy) head (ids.eraseIdx (k + 1)) := by
  refine ⟨rep.1.eraseIdx (k + 1),
    rep.2.1.trans (eraseIdx_succ_head? ids k).symm, ?_⟩
  intro i hi
  by_cases hik : i < k + 1
  · have hio : i < ids.length := by omega
    obtain ⟨node, hn, hnext⟩ := rep.2.2 i hio
    refine ⟨{ node with next := if i = k then ids[k + 1 + 1]? else node.next }, ?_, ?_⟩
    · have hcell := deleteAfter_old_cell store rep k hk hy i hio node hn
      rw [List.getElem_eraseIdx, dite_eq_left hik]
      exact hcell
    · rw [List.getElem?_eraseIdx]
      by_cases hik' : i = k
      · subst i
        simp
      · have hlt : i + 1 < k + 1 := by omega
        simp only [ite_eq_right hik', ite_eq_left hlt]
        exact hnext
  · by_cases hkn : k + 1 < ids.length
    · have hlen : (ids.eraseIdx (k + 1)).length = ids.length - 1 :=
        List.length_eraseIdx_of_lt hkn
      have hio : i + 1 < ids.length := by omega
      obtain ⟨node, hn, hnext⟩ := rep.2.2 (i + 1) hio
      refine ⟨{ node with next :=
        if i + 1 = k then ids[k + 1 + 1]? else node.next }, ?_, ?_⟩
      · have hcell := deleteAfter_old_cell store rep k hk hy (i + 1) hio node hn
        rw [List.getElem_eraseIdx, dite_eq_right hik]
        exact hcell
      · rw [List.getElem?_eraseIdx]
        simp only [ite_eq_right (show i + 1 ≠ k by omega),
          ite_eq_right (show ¬i + 1 < k + 1 by omega)]
        exact hnext
    · exfalso
      have herase : ids.eraseIdx (k + 1) = ids :=
        List.eraseIdx_of_length_le (by omega)
      rw [herase] at hi
      omega

/-- Deleting a successor erases the corresponding content entry. -/
theorem deleteAfter_contents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (ids : List (Fin capacity)) (k : Nat) (hk : k < ids.length)
    (hy : (store.get ids[k]).isSome) :
    contents (deleteAfter store ids[k] hy) (ids.eraseIdx (k + 1)) =
      (contents store ids).eraseIdx (k + 1) := by
  have hmap : contents (deleteAfter store ids[k] hy) (ids.eraseIdx (k + 1)) =
      (ids.eraseIdx (k + 1)).map (fun i => (store.get i).map Node.payload) :=
    List.map_congr_left fun i _ => deleteAfter_payload store ids[k] hy i
  rw [hmap]
  show (ids.eraseIdx (k + 1)).map (fun i => (store.get i).map Node.payload) = _
  rw [map_eraseIdx]
  rfl

/-- Fuel-bounded search following next pointers: the first visited identity
whose payload equals `target`, if reached within `fuel` steps. -/
def searchAux {α : Type u} {capacity : Nat} [DecidableEq α]
    (store : Vector (Option (Node α (Fin capacity))) capacity) (target : α) :
    Nat → Option (Fin capacity) → Option (Fin capacity)
  | 0, _ => none
  | _ + 1, none => none
  | fuel + 1, some i =>
    match store.get i with
    | none => none
    | some node =>
      if node.payload = target then some i
      else searchAux store target fuel node.next

/-- Search a list for the first identity whose payload equals `target`,
following next pointers from the head; the fuel is the pool capacity. -/
def search {α : Type u} {capacity : Nat} [DecidableEq α]
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (target : α) : Option (Fin capacity) :=
  searchAux store target capacity head

/-- With at least as much fuel as the represented length, fuel-bounded search
is `List.find?` over the represented identities. -/
theorem searchAux_eq_find? {α : Type u} {capacity : Nat} [DecidableEq α]
    (store : Vector (Option (Node α (Fin capacity))) capacity) (target : α)
    (fuel : Nat) (head : Option (Fin capacity)) (ids : List (Fin capacity))
    (rep : Represents store head ids) (hlen : ids.length ≤ fuel) :
    searchAux store target fuel head =
      ids.find? (fun i => decide ((store.get i).map Node.payload = some target)) := by
  revert head ids
  induction fuel with
  | zero =>
    intro head ids rep hlen
    cases ids with
    | nil => rfl
    | cons a rest => simp at hlen
  | succ fuel ih =>
    intro head ids rep hlen
    cases ids with
    | nil =>
      have hhead : head = none := rep.2.1
      subst head
      rfl
    | cons a rest =>
      obtain ⟨node, hn, htail⟩ := represents_cons rep
      have hhead : head = some a := rep.2.1
      subst head
      have hlen' : rest.length ≤ fuel := by
        rw [List.length_cons] at hlen
        omega
      have ih' := ih node.next rest htail hlen'
      have hL : searchAux store target (fuel + 1) (some a) =
          if node.payload = target then some a
          else searchAux store target fuel node.next := by
        simp only [searchAux, hn]
      have hR : (a :: rest).find?
            (fun i => decide ((store.get i).map Node.payload = some target)) =
          if node.payload = target then some a
          else rest.find?
            (fun i => decide ((store.get i).map Node.payload = some target)) := by
        by_cases hp : node.payload = target <;> simp [hn, hp]
      rw [hL, hR]
      by_cases hp : node.payload = target <;> simp [hp, ih']

/-- A represented identity list is no longer than the pool capacity: its
identities are distinct elements of `Fin capacity`. -/
theorem represents_length_le_capacity {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) :
    ids.length ≤ capacity := by
  have h := List.Nodup.length_le_card rep.1
  rwa [Fintype.card_fin] at h

/-- Search agrees with `List.find?` over the represented identities. -/
theorem search_eq_find? {α : Type u} {capacity : Nat} [DecidableEq α]
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (target : α) (ids : List (Fin capacity))
    (rep : Represents store head ids) :
    search store head target =
      ids.find? (fun i => decide ((store.get i).map Node.payload = some target)) :=
  searchAux_eq_find? store target capacity head ids rep
    (represents_length_le_capacity rep)

/-- A successful search returns a represented identity carrying the target payload. -/
theorem search_eq_some {α : Type u} {capacity : Nat} [DecidableEq α]
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (target : α) (ids : List (Fin capacity))
    (rep : Represents store head ids)
    {x : Fin capacity} (h : search store head target = some x) :
    x ∈ ids ∧ (store.get x).map Node.payload = some target := by
  rw [search_eq_find? store head target ids rep] at h
  exact ⟨List.mem_of_find?_eq_some h, by
    have hp := List.find?_some h
    simpa using hp⟩

/-- Search fails exactly when no represented payload equals the target. -/
theorem search_eq_none_iff {α : Type u} {capacity : Nat} [DecidableEq α]
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (target : α) (ids : List (Fin capacity))
    (rep : Represents store head ids) :
    search store head target = none ↔
      ∀ i ∈ ids, (store.get i).map Node.payload ≠ some target := by
  rw [search_eq_find? store head target ids rep, List.find?_eq_none]
  constructor
  · intro h i hi
    have := h i hi
    simpa using this
  · intro h i hi
    have := h i hi
    simpa using this

end Cslib.Algorithms.Lean.SinglyLinkedList
