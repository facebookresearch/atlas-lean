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

/-- **Singly linked list node.** A singly linked list node with payloads in $\alpha$ and identities
in $\iota$ consists of a payload in $\alpha$ (the key together with any satellite data) and a next
pointer, which is either an identity in $\iota$ or NIL. -/
structure Node (α : Type u) (ι : Type v) where
  /-- The full payload, including any key and satellite data. -/
  payload : α
  /-- Next node identity, or NIL at the tail. -/
  next : Option ι
deriving DecidableEq, Repr

/-- **Store representing a singly linked list.** Fix a capacity $n$, let a store assign to each
identity below $n$ either nothing or a singly linked list node whose next pointer is an identity
below $n$ or NIL, and let the head be an identity below $n$ or NIL. The store and head represent
the list of identities $i_0, \dots, i_{k-1}$ when these identities are pairwise distinct, the head
is $i_0$ (and NIL when $k = 0$), and for each $j < k$ the store entry at $i_j$ is a node whose next
pointer is $i_{j+1}$ if $j + 1 < k$ and NIL otherwise. -/
def Represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity)) : Prop :=
  ids.Nodup ∧ head = ids.head? ∧
    ∀ (i : Nat) (hi : i < ids.length), ∃ node,
      store.get ids[i] = some node ∧
      node.next = ids[i + 1]?

/-- **Representation of the empty singly linked list.** Fix a capacity $n$ and let $s$ be any store
assigning to each identity below $n$ either nothing or a singly linked list node. Then $s$ with
head NIL represents the empty list of identities. -/
theorem represents_nil {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) :
    Represents store none ([] : List (Fin capacity)) := by
  refine ⟨List.nodup_nil, rfl, ?_⟩
  intro i hi
  simp at hi

/-- **Represented identities hold nodes.** Fix a capacity $n$, let $s$ be a store assigning to
each identity below $n$ either nothing or a singly linked list node, and let $\mathrm{head}$ be an
identity below $n$ or NIL. If $s$ and $\mathrm{head}$ represent the list of identities
$i_0, \dots, i_{k-1}$, then for every identity $i$ in this list the store entry $s(i)$ is a
node. -/
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

/-- **Payload list of a singly linked list store.** Fix a capacity $n$ and let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node (a payload
together with a next pointer that is an identity below $n$ or NIL). For a list of identities
$i_0, \dots, i_{m-1}$ below $n$, the contents of $s$ at this list are the list
$c_0, \dots, c_{m-1}$, where $c_j$ is the payload of $s(i_j)$ when $s(i_j)$ is a node and $c_j$ is
nothing (marking an unallocated cell) when $s(i_j)$ is nothing. -/
def contents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (ids : List (Fin capacity)) : List (Option α) :=
  ids.map fun i => (store.get i).map Node.payload

/-- **The payload list has one entry per identity.** Fix a capacity $n$ and let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node. For every list
$L$ of identities below $n$, the contents of $s$ at $L$ have the same length as $L$. -/
@[simp]
theorem contents_length {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (ids : List (Fin capacity)) :
    (contents store ids).length = ids.length :=
  List.length_map _

/-- **The payload list depends only on the listed cells.** Fix a capacity $n$ and let $s$ and $s'$
be stores assigning to each identity below $n$ either nothing or a singly linked list node. If $L$
is a list of identities below $n$ and $s'(i) = s(i)$ for every $i$ in $L$, then the contents of
$s'$ at $L$ equal the contents of $s$ at $L$. -/
theorem contents_congr {α : Type u} {capacity : Nat}
    {store store' : Vector (Option (Node α (Fin capacity))) capacity}
    {ids : List (Fin capacity)}
    (h : ∀ i ∈ ids, store'.get i = store.get i) :
    contents store' ids = contents store ids := by
  unfold contents
  exact List.map_congr_left fun i hi => by rw [h i hi]

/-- **Represented lists have no missing contents.** Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, and let
$\mathrm{head}$ be an identity below $n$ or NIL. If $s$ and $\mathrm{head}$ represent the list of
identities $i_0, \dots, i_{k-1}$, then every entry of the contents of $s$ at $i_0, \dots, i_{k-1}$
is a payload rather than nothing. -/
theorem represents_contents_isSome {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) :
    ∀ x ∈ contents store ids, x.isSome = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [Option.isSome_map]
  exact represents_allocated rep hi

/-- **Prepending a node to a singly linked list.** Fix a capacity $n$, let a store assign to each
identity below $n$ either nothing or a singly linked list node, let the head be an identity below
$n$ or NIL, and let $x$ be an identity whose store entry is a node. Prepending $x$ replaces the
store entry at $x$ by the same node with its next pointer set to the head, leaves every other entry
unchanged, and returns the updated store together with the new head $x$. -/
def prepend {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome) :
    Vector (Option (Node α (Fin capacity))) capacity × Option (Fin capacity) :=
  (store.set x.val (some { (store.get x).get hx with next := head }) x.isLt, some x)

/-- **Prepending makes the node the head.** Fix a capacity $n$, let $s$ be a store assigning to
each identity below $n$ either nothing or a singly linked list node, let $\mathrm{head}$ be an
identity below $n$ or NIL, and let $x$ be an identity such that $s(x)$ is a node. Then the head
returned by Prepend on $s$, $\mathrm{head}$ and $x$ is $x$. -/
theorem prepend_head {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome) :
    (prepend store head x hx).2 = some x :=
  rfl

/-- **Store after prepending to a singly linked list.** Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, let
$\mathrm{head}$ be an identity below $n$ or NIL, and let $x$ be an identity such that $s(x)$ is a
node. Then for every identity $z$ below $n$, the entry at $z$ of the store returned by Prepend on
$s$, $\mathrm{head}$ and $x$ is the node $s(x)$ with its next pointer replaced by $\mathrm{head}$
when $z = x$, and is $s(z)$ when $z \ne x$. -/
theorem prepend_get {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome) (z : Fin capacity) :
    (prepend store head x hx).1.get z =
      if x = z then some { (store.get x).get hx with next := head } else store.get z := by
  exact vector_get_set store x z _

/-- **Frame property of prepending to a singly linked list.** Let $S$ be a store assigning to
each identity below $n$ either nothing or a singly linked list node, let $h$ be an identity below
$n$ or NIL, and let $x$ be an identity whose store entry is a node. For every identity
$z \ne x$, cell $z$ of the store obtained by prepending $x$ to the list with head $h$ equals
cell $z$ of $S$. -/
theorem prepend_frame {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome) (z : Fin capacity) (hz : x ≠ z) :
    (prepend store head x hx).1.get z = store.get z := by
  rw [prepend_get, ite_eq_right hz]

/-- **The prepended node points at the old head.** Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, let
$\mathrm{head}$ be an identity below $n$ or NIL, and let $x$ be an identity such that $s(x)$ is a
node. Then the entry at $x$ of the store returned by Prepend on $s$, $\mathrm{head}$ and $x$ is the
node $s(x)$ with its payload kept and its next pointer replaced by $\mathrm{head}$. -/
theorem prepend_node {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome) :
    (prepend store head x hx).1.get x =
      some { (store.get x).get hx with next := head } := by
  rw [prepend_get, ite_eq_left rfl]

/-- **Prepending conses onto the represented list.** Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, let
$\mathrm{head}$ be an identity below $n$ or NIL, and let $x$ be an identity such that $s(x)$ is a
node. If $s$ and $\mathrm{head}$ represent the list of identities $i_0, \dots, i_{k-1}$ and $x$ is
none of $i_0, \dots, i_{k-1}$, then the store and head returned by Prepend on $s$, $\mathrm{head}$
and $x$ represent the list $x, i_0, \dots, i_{k-1}$. -/
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

/-- **Contents after prepending to a singly linked list.** Let $S$ be a store assigning to each
identity below $n$ either nothing or a singly linked list node, let $h$ be an identity below $n$
or NIL, let $x$ be an identity whose store entry is a node with payload $a$, and let
$(i_0, \dots, i_{m-1})$ be a list of identities below $n$ not containing $x$. Then the contents,
at the list $(x, i_0, \dots, i_{m-1})$, of the store obtained by prepending $x$ to the list with
head $h$ are the present payload $a$ followed by the contents of $S$ at the list
$(i_0, \dots, i_{m-1})$. -/
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

/-- **Inserting a node after another in a singly linked list.** Let a store $S$ assign to each
identity below $n$ either nothing or a singly linked list node whose next pointer is an identity
below $n$ or NIL, and let $x$ and $y$ be identities whose store entries are nodes. Inserting $x$
after $y$ first replaces cell $x$ by the node of $x$ with next pointer replaced by the next
pointer of $y$ in $S$, then, in the store so obtained, replaces the next pointer of the node in
cell $y$ by $x$, and returns the resulting store. -/
def insertAfter {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y x : Fin capacity)
    (hy : (store.get y).isSome) (hx : (store.get x).isSome) :
    Vector (Option (Node α (Fin capacity))) capacity :=
  let store₁ := store.set x.val
    (some { (store.get x).get hx with next := ((store.get y).get hy).next }) x.isLt
  store₁.set y.val ((store₁.get y).map fun node => { node with next := some x }) y.isLt

/-- **Cells after singly-linked-list insertion.** Let $S$ be a store assigning to each identity
below $n$ either nothing or a singly linked list node, let $x$ and $y$ be identities whose store
entries are nodes, and let $z$ be any identity. Let $c$ be the node of $x$ in $S$ with next
pointer replaced by the next pointer of $y$ in $S$ if $z = x$, and the content of cell $z$ in $S$
otherwise. Then cell $z$ of the store obtained by inserting $x$ after $y$ is $c$ with next pointer
replaced by $x$ if $z = y$, and $c$ otherwise.

No distinctness of $x$ and $y$ is assumed. -/
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

/-- **Frame property of singly-linked-list insertion.** Let $S$ be a store assigning to each
identity below $n$ either nothing or a singly linked list node, and let $x$ and $y$ be identities
whose store entries are nodes. For every identity $z$ with $z \ne y$ and $z \ne x$, cell $z$ of
the store obtained by inserting $x$ after $y$ equals cell $z$ of $S$. -/
theorem insertAfter_frame {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y x : Fin capacity)
    (hy : (store.get y).isSome) (hx : (store.get x).isSome) (z : Fin capacity)
    (hyz : y ≠ z) (hxz : x ≠ z) :
    (insertAfter store y x hy hx).get z = store.get z := by
  rw [insertAfter_get, ite_eq_right hyz, ite_eq_right hxz]

/-- **Singly-linked-list insertion preserves payloads.** Let $S$ be a store assigning to each
identity below $n$ either nothing or a singly linked list node, and let $x$ and $y$ be identities
whose store entries are nodes. For every identity $z$, cell $z$ of the store obtained by inserting
$x$ after $y$ is empty exactly when cell $z$ of $S$ is empty, and otherwise holds a node with the
same payload as the node in cell $z$ of $S$. -/
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

/-- **Insertion into a represented singly linked list.** Suppose the store $S$ with head $h$
represents the list of distinct identities $(i_0, \dots, i_{m-1})$. Let $k < m$, assume that the
store entry of $i_k$ is a node, and let $x$ be an identity whose store entry is a node and which
is not among $i_0, \dots, i_{m-1}$. Then the store obtained by inserting $x$ after $i_k$, with
the same head $h$, represents the list $(i_0, \dots, i_k, x, i_{k+1}, \dots, i_{m-1})$. -/
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

/-- **Contents after singly-linked-list insertion.** Let $S$ be a store assigning to each identity
below $n$ either nothing or a singly linked list node, let $(i_0, \dots, i_{m-1})$ be a list of
identities below $n$, let $k < m$, and let $x$ be an identity such that the store entries of $x$
and $i_k$ are nodes, the node of $x$ having payload $a$. Then the contents of the store obtained
by inserting $x$ after $i_k$ at the list $(i_0, \dots, i_k, x, i_{k+1}, \dots, i_{m-1})$ equal
the contents of $S$ at $(i_0, \dots, i_{m-1})$ with the present payload $a$ inserted as entry
$k + 1$ (counting from $0$).

No representation or distinctness hypothesis is assumed. -/
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

/-- **Deleting the head of a singly linked list.** Let a store assign to each identity below $n$
either nothing or a singly linked list node whose next pointer is an identity below $n$ or NIL,
and let the head be an identity below $n$ or NIL. Deleting the head returns the store unchanged
together with a new head: NIL if the head is NIL or the store entry at the head is empty, and
otherwise the next pointer of the node stored at the head. -/
def deleteHead {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) :
    Vector (Option (Node α (Fin capacity))) capacity × Option (Fin capacity) :=
  (store, head.bind fun h => (store.get h).bind fun node => node.next)

/-- **Deleting the head removes the first identity.** Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, and suppose that
$s$ with head $h$ represents the list of identities $L$, where $h$ is an identity below $n$ or NIL.
Let $(s', h')$ be the store and head returned by deleting the head of $s$ with head $h$. Then $s'$
with head $h'$ represents $L$ with its first entry removed, which is the empty list when $L$ is
empty. -/
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

/-- **Deleting the successor in a singly linked list.** Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node whose next
pointer is an identity below $n$ or NIL, and let $y$ be an identity such that $s(y)$ is a node.
Deleting after $y$ returns the store that agrees with $s$ except at $y$, where it holds the node
$s(y)$ with its next pointer replaced as follows: if the next pointer of $s(y)$ is an identity $m$
and $s(m)$ is a node, the new next pointer is the next pointer of $s(m)$; otherwise it is NIL.

The removed node stays allocated in the store; at the tail the links are unchanged. -/
def deleteAfter {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y : Fin capacity) (hy : (store.get y).isSome) :
    Vector (Option (Node α (Fin capacity))) capacity :=
  store.set y.val (some { (store.get y).get hy with
    next := ((store.get y).get hy).next.bind
      fun n => (store.get n).bind fun node => node.next }) y.isLt

/-- **Cells after deleting a successor.** Fix a capacity $n$, let $s$ be a store assigning to each
identity below $n$ either nothing or a singly linked list node, let $y$ be an identity such that
$s(y)$ is a node, and let $s'$ be the store obtained from $s$ by deleting the successor of $y$.
Let $c$ be the node $s(y)$ with its next pointer replaced by the next pointer of $s(m)$ if the
next pointer of $s(y)$ is an identity $m$ such that $s(m)$ is a node, and by NIL otherwise. Then
for every identity $z$, $s'(z)$ is the node $c$ if $z = y$, and $s'(z) = s(z)$ if $z \ne y$. -/
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

/-- **Deleting a successor leaves other cells unchanged.** Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, let $y$ be an
identity such that $s(y)$ is a node, and let $s'$ be the store obtained from $s$ by deleting the
successor of $y$. Then $s'(z) = s(z)$ for every identity $z \ne y$. -/
theorem deleteAfter_frame {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (y : Fin capacity) (hy : (store.get y).isSome) (z : Fin capacity)
    (hyz : y ≠ z) :
    (deleteAfter store y hy).get z = store.get z := by
  rw [deleteAfter_get, ite_eq_right hyz]

/-- **Deleting a successor preserves payloads.** Fix a capacity $n$, let $s$ be a store assigning
to each identity below $n$ either nothing or a singly linked list node, let $y$ be an identity
such that $s(y)$ is a node, and let $s'$ be the store obtained from $s$ by deleting the successor
of $y$. Then for every identity $z$, either $s(z)$ and $s'(z)$ are both nothing, or both are nodes
with the same payload. -/
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

/-- **Deleting a successor removes it from the represented list.** Fix a capacity $n$, let $s$ be a
store assigning to each identity below $n$ either nothing or a singly linked list node, and
suppose that $s$ with head $h$ represents the list of identities $L = (i_0, \dots, i_{m-1})$. Let
$k < m$ be such that $s(i_k)$ is a node, and let $s'$ be the store obtained from $s$ by deleting
the successor of $i_k$. Then $s'$ with the same head $h$ represents the list obtained from $L$ by
removing the entry at position $k + 1$. Positions count from $0$, and at the tail ($k + 1 = m$)
the list is unchanged. -/
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

/-- **Contents after deleting a successor.** Fix a capacity $n$, let $s$ be a store assigning to
each identity below $n$ either nothing or a singly linked list node, let
$L = (i_0, \dots, i_{m-1})$ be a list of identities below $n$, and let $k < m$ be such that
$s(i_k)$ is a node. Let $s'$ be the store obtained from $s$ by deleting the successor of $i_k$.
Then the contents of $s'$ at the list obtained from $L$ by removing the entry at position $k + 1$
equal the list obtained from the contents of $s$ at $L$ by removing the entry at position $k + 1$.
Positions count from $0$, and nothing is removed when $k + 1 = m$. -/
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

/-- **Fuel-bounded search in a singly-linked list.** Given a node pool with $n$ cells, a target
payload $t$, a fuel $f \in \mathbb{N}$ and a start $h$ that is either an identity in
$\{0, \dots, n-1\}$ or NIL, fuel-bounded search for $t$ from $h$ with fuel $f$ returns nothing
if $f = 0$ or $h$ is NIL. Otherwise $h$ is an identity $i$: the search returns nothing if cell
$i$ is unallocated, returns $i$ if the node in cell $i$ has payload $t$, and otherwise continues
from the next pointer of that node with fuel $f - 1$. -/
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

/-- **Search in a singly-linked list.** Given a node pool with $n$ cells, a head $h$ that is
either an identity in $\{0, \dots, n-1\}$ or NIL, and a target payload $t$, the search for $t$
from $h$ is fuel-bounded search for $t$ from $h$ with fuel $n$. It follows next pointers from
$h$ and returns the first visited identity whose node has payload $t$, returning nothing if it
reaches NIL or an unallocated cell first, or if $n$ steps run out. -/
def search {α : Type u} {capacity : Nat} [DecidableEq α]
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (target : α) : Option (Fin capacity) :=
  searchAux store target capacity head

/-- **Fuel-bounded search finds the first matching represented identity.** Suppose a node pool
represents, from the head $h$, the list of distinct identities $\ell$. Then for every target
payload $t$ and every fuel $f$ with $f \ge |\ell|$, fuel-bounded search for $t$ from $h$ with
fuel $f$ returns the first identity in $\ell$ whose cell holds a node with payload $t$, and
returns nothing if no identity in $\ell$ has this property. -/
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

/-- **Represented lists fit in the store.** Fix a capacity $n$, let $s$ be a store assigning to
each identity below $n$ either nothing or a singly linked list node, and let $\mathrm{head}$ be an
identity below $n$ or NIL. If $s$ and $\mathrm{head}$ represent the list of identities
$i_0, \dots, i_{k-1}$, then $k \le n$.

The identities are pairwise distinct and there are only $n$ of them. -/
theorem represents_length_le_capacity {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) :
    ids.length ≤ capacity := by
  have h := List.Nodup.length_le_card rep.1
  rwa [Fintype.card_fin] at h

/-- **Search finds the first matching represented identity.** If a node pool represents, from the
head $h$, the list of distinct identities $\ell$, then for every target payload $t$ the search
for $t$ from $h$ returns the first identity in $\ell$ whose cell holds a node with payload $t$,
and returns nothing if no identity in $\ell$ has this property. -/
theorem search_eq_find? {α : Type u} {capacity : Nat} [DecidableEq α]
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (target : α) (ids : List (Fin capacity))
    (rep : Represents store head ids) :
    search store head target =
      ids.find? (fun i => decide ((store.get i).map Node.payload = some target)) :=
  searchAux_eq_find? store target capacity head ids rep
    (represents_length_le_capacity rep)

/-- **A successful search returns a matching represented identity.** If a node pool represents,
from the head $h$, the list of distinct identities $\ell$, and the search for a target payload
$t$ from $h$ returns an identity $x$, then $x$ belongs to $\ell$ and cell $x$ holds a node with
payload $t$. -/
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

/-- **Search fails exactly when no represented node has the target payload.** If a node pool
represents, from the head $h$, the list of distinct identities $\ell$, then for every target
payload $t$ the search for $t$ from $h$ returns nothing if and only if no identity in $\ell$ has
a cell holding a node with payload $t$. -/
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
