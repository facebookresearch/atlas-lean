/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Init.Data.Vector.Lemmas
public import Mathlib.Data.List.Nodup

/-!
# Doubly-linked list prepend with pointer-event costs

`Node` has an identity-independent payload and optional next/previous pointers.
`Represents` relates a finite allocated node pool and header to an ordered list
of distinct node identities. `listPrepend` implements CLRS fourth edition,
section 10.2, printed page 260, LIST-PREPEND, including its update order.

The caller supplies an allocated node, not an allocator. Execution requires
only access to that node and any old head. Freshness is a representation-proof
premise, not an execution premise. The nonempty branch reads the carried store
after both writes at the supplied node, even when that node is the old head.

The same computation counts one event per pointer assignment and per old-head
NIL test: four events for an empty header, five otherwise. Array indexing,
record reads, erased proofs and return are free in this model. These are not
claims about native constant time, physical allocation, space or full RAM cost.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DoublyLinkedList

universe u v

/-- **Doubly linked list node.** A doubly linked list node with payloads in $\alpha$ and identities
in $\iota$ consists of a payload in $\alpha$ (the key together with any satellite data), a next
pointer and a previous pointer, each of which is either an identity in $\iota$ or NIL. -/
public structure Node (α : Type u) (ι : Type v) where
  /-- The full payload, including any key and satellite data. -/
  payload : α
  /-- Next node identity, or NIL at the tail. -/
  next : Option ι
  /-- Previous node identity, or NIL at the head. -/
  prev : Option ι
deriving DecidableEq, Repr

/-- **Store representing a doubly linked list.** Let a store assign to each identity below $n$
either nothing or a doubly linked list node whose pointers are identities below $n$ or NIL, and
let the head be an identity below $n$ or NIL. The store and head represent the list of identities
$i_0, \dots, i_{k-1}$ when these identities are pairwise distinct, the head is $i_0$ (and NIL
when $k = 0$), and for each $j < k$ the store entry at $i_j$ is a node whose previous pointer is
NIL if $j = 0$ and $i_{j-1}$ otherwise, and whose next pointer is $i_{j+1}$ if $j + 1 < k$ and
NIL otherwise. -/
public def Represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity)) : Prop :=
  ids.Nodup ∧ head = ids.head? ∧
    ∀ (i : Nat) (hi : i < ids.length), ∃ node,
      store.get ids[i] = some node ∧
      node.prev = (if i = 0 then none else ids[i - 1]?) ∧
      node.next = ids[i + 1]?

private lemma vector_get_set {α : Type u} {n : Nat}
    (xs : Vector α n) (i j : Fin n) (a : α) :
    (xs.set i.val a i.isLt).get j = if i = j then a else xs.get j := by
  change (xs.set i.val a i.isLt)[j.val] = if i = j then a else xs[j.val]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff]

/-- **Prepending a node to a doubly linked list.** Let a store assign to each identity below $n$
either nothing or a doubly linked list node whose pointers are identities below $n$ or NIL, let
the head be an identity below $n$ or NIL, and let $x$ be an identity whose store entry is a node,
where the store entry of the head is also a node when the head is not NIL. The procedure sets the
next pointer of $x$ to the head, then sets the previous pointer of $x$ to NIL, then tests whether
the head is NIL; if it is not, it sets the previous pointer of the node at the head (read after
the two writes at $x$) to $x$. Finally it makes $x$ the new head and returns the updated store
together with the head $x$. One time unit is charged for each pointer assignment and for the NIL
test, so the cost is $4$ when the head is NIL and $5$ otherwise. -/
public def listPrepend {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) :
    TimeM Nat (Vector (Option (Node α (Fin capacity))) capacity × Option (Fin capacity)) := do
  let originalX := (store.get x).get hx
  TimeM.tick 1
  let nextX := { originalX with next := head }
  let store1 := store.set x.val (some nextX) x.isLt
  TimeM.tick 1
  let prevX := { nextX with prev := none }
  let store2 := store1.set x.val (some prevX) x.isLt
  TimeM.tick 1
  match he : head with
  | none =>
    TimeM.tick 1
    pure (store2, some x)
  | some h =>
    have hAllocated : (store2.get h).isSome := by
      change (store1.set x.val (some prevX) x.isLt)[h.val].isSome = true
      rw [Vector.getElem_set]
      split
      · rfl
      · change store1[h.val].isSome = true
        rw [Vector.getElem_set]
        split
        · rfl
        · exact hh h he
    let currentH := (store2.get h).get hAllocated
    TimeM.tick 1
    let store3 := store2.set h.val (some { currentH with prev := some x }) h.isLt
    TimeM.tick 1
    pure (store3, some x)

/-- **Prepending makes the supplied node the head.** Fix a capacity $n$ and let $s$ be a store
assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Then the head returned by List Prepend on $s$,
$\mathrm{head}$ and $x$ is $x$. -/
public theorem listPrepend_head {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) :
    (listPrepend store head x hx hh).ret.2 = some x := by
  cases head <;> simp [listPrepend]

/-- **Exact cost of doubly linked list prepend.** Let a store assign to each identity below $n$
either nothing or a doubly linked list node, let the head be an identity below $n$ or NIL, and let
$x$ be an identity whose store entry is a node, where the store entry of the head is also a node
when the head is not NIL. Then prepending $x$ costs exactly $5$ time units if the head is not NIL
and exactly $4$ if it is NIL, counting one unit per pointer assignment and per NIL test of the
old head. -/
public theorem listPrepend_time {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) :
    (listPrepend store head x hx hh).time = if head.isSome then 5 else 4 := by
  cases head <;> simp [listPrepend]

/-- **Result of doubly-linked list prepend.** Fix a capacity $n$ and let $s$ be a store assigning to
each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an identity, and let
$x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an identity,
$s(\mathrm{head})$ is a node. Let $u$ be $s$ with the cell at $x$ replaced by the node $s(x)$ with
next pointer $\mathrm{head}$ and previous pointer NIL. Then List Prepend on $s$, $\mathrm{head}$ and
$x$ returns the head $x$ together with the store $u$ when $\mathrm{head}$ is NIL, and, when
$\mathrm{head}$ is an identity $h$, together with the store obtained from $u$ by replacing its cell
at $h$ with the node $u(h)$ with previous pointer $x$ (leaving the cell empty if $u(h)$ is
nothing).

This holds also when $h = x$. -/
public theorem listPrepend_ret {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) :
    let updated := store.set x.val
      (some { (store.get x).get hx with next := head, prev := none }) x.isLt
    (listPrepend store head x hx hh).ret =
      (match head with
       | none => updated
       | some h => updated.set h.val
           ((updated.get h).map fun node => { node with prev := some x }) h.isLt,
       some x) := by
  cases head with
  | none => simp [listPrepend]
  | some h =>
    simp only [listPrepend, TimeM.ret_bind, TimeM.ret_pure, Vector.set_set]
    apply congrArg (fun value => ((store.set x.val
      (some { (store.get x).get hx with next := some h, prev := none }) x.isLt).set
        h.val value h.isLt, some x))
    exact congrArg (Option.map fun (node : Node α (Fin capacity)) =>
      { node with prev := some x }) (Option.some_get _)

/-- **Cells after doubly-linked list prepend.** Fix a capacity $n$ and let $s$ be a store assigning
to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an identity, and
let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an identity,
$s(\mathrm{head})$ is a node. Let $s'$ be the store returned by List Prepend on $s$, $\mathrm{head}$
and $x$. For every identity $z$, let $c$ be the node $s(x)$ with next pointer $\mathrm{head}$ and
previous pointer NIL if $z = x$, and $c = s(z)$ otherwise. Then $s'(z)$ is $c$ with previous pointer
$x$ (nothing, if $c$ is nothing) when $\mathrm{head} = z$, and $s'(z) = c$ otherwise. -/
public theorem listPrepend_get {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) (z : Fin capacity) :
    (listPrepend store head x hx hh).ret.1.get z =
      let cell := if x = z then
        some { (store.get x).get hx with next := head, prev := none } else store.get z
      if head = some z then cell.map fun node => { node with prev := some x } else cell := by
  rw [listPrepend_ret]
  cases head with
  | none => simp [vector_get_set]
  | some h =>
    by_cases hz : h = z <;> by_cases xz : x = z <;> simp_all [vector_get_set]

/-- **Doubly-linked list prepend leaves other cells unchanged.** Fix a capacity $n$ and let $s$ be a
store assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Let $s'$ be the store returned by List Prepend on $s$,
$\mathrm{head}$ and $x$. Then $s'(z) = s(z)$ for every identity $z$ with $z \ne x$ and
$\mathrm{head} \ne z$. -/
public theorem listPrepend_frame {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) (z : Fin capacity)
    (xz : x ≠ z) (hz : head ≠ some z) :
    (listPrepend store head x hx hh).ret.1.get z = store.get z := by
  rw [listPrepend_get]
  simp only [xz, hz, ↓reduceIte]

/-- **Doubly-linked list prepend preserves allocation.** Fix a capacity $n$ and let $s$ be a store
assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Let $s'$ be the store returned by List Prepend on $s$,
$\mathrm{head}$ and $x$. Then for every identity $z$, $s'(z)$ is a node if and only if $s(z)$ is a
node. -/
public theorem listPrepend_allocated {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) (z : Fin capacity) :
    ((listPrepend store head x hx hh).ret.1.get z).isSome = (store.get z).isSome := by
  rw [listPrepend_get]
  by_cases xz : x = z
  · subst z
    by_cases hz : head = some x <;> simp [hz, hx]
  · by_cases hz : head = some z <;> simp [xz, hz]

/-- **Doubly-linked list prepend preserves payloads.** Fix a capacity $n$ and let $s$ be a store
assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Let $s'$ be the store returned by List Prepend on $s$,
$\mathrm{head}$ and $x$. Then for every identity $z$, either $s(z)$ and $s'(z)$ are both nothing, or
both are nodes with the same payload. -/
public theorem listPrepend_payload {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) (z : Fin capacity) :
    ((listPrepend store head x hx hh).ret.1.get z).map Node.payload =
      (store.get z).map Node.payload := by
  rw [listPrepend_get]
  by_cases xz : x = z
  · subst z
    have hp := congrArg (Option.map Node.payload) (Option.some_get hx)
    simp only [ite_true]
    by_cases hz : head = some x <;>
      simpa only [hz, ite_true, ite_false, Option.map_some] using hp
  · by_cases hz : head = some z <;>
      simp only [xz, hz, ite_true, ite_false, Option.map_map, Function.comp_def]

/-- **Pointers of the node prepended to a doubly-linked list.** Fix a capacity $n$ and let $s$ be a
store assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Suppose moreover that $\mathrm{head}$ is not $x$ (it may be
NIL). Let $s'$ be the store returned by List Prepend on $s$, $\mathrm{head}$ and $x$. Then $s'(x)$
is the node $s(x)$ with next pointer $\mathrm{head}$ and previous pointer NIL. -/
public theorem listPrepend_node {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) (fresh : head ≠ some x) :
    (listPrepend store head x hx hh).ret.1.get x =
      some { (store.get x).get hx with next := head, prev := none } := by
  rw [listPrepend_get]
  simp only [ite_true, fresh, ite_false]

/-- **Old head after doubly-linked list prepend.** Fix a capacity $n$ and let $s$ be a store
assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Suppose moreover that $\mathrm{head}$ is an identity $h$
with $h \ne x$. Let $s'$ be the store returned by List Prepend on $s$, $\mathrm{head}$ and $x$.
Then $s'(h)$ is the node $s(h)$ with previous pointer $x$. -/
public theorem listPrepend_oldHead {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) (h : Fin capacity)
    (he : head = some h) (xh : x ≠ h) :
    (listPrepend store head x hx hh).ret.1.get h =
      some { (store.get h).get (hh h he) with prev := some x } := by
  rw [listPrepend_get]
  simp only [xh, ite_false, he, ite_true]
  exact (congrArg (Option.map fun (node : Node α (Fin capacity)) =>
    { node with prev := some x }) (Option.some_get (hh h he))).symm

private lemma represents_head_mem {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) {h : Fin capacity} (he : head = some h) : h ∈ ids := by
  have hp : ids.head? = some h := rep.2.1.symm.trans he
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp hp
  exact List.mem_cons_self

private lemma represents_head_allocated {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) (h : Fin capacity) (he : head = some h) :
    (store.get h).isSome := by
  obtain ⟨tail, hid⟩ := List.head?_eq_some_iff.mp (rep.2.1.symm.trans he)
  obtain ⟨node, hn, _, _⟩ := rep.2.2 0 (by simp [hid])
  simpa [hid, hn] using congrArg Option.isSome hn

private lemma represents_head_zero {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) (h0 : 0 < ids.length) : head = some ids[0] := by
  rw [rep.2.1]
  cases ids with
  | nil => simp at h0
  | cons a tail => rfl

private lemma represents_later_not_head {α : Type u} {capacity : Nat}
    {store : Vector (Option (Node α (Fin capacity))) capacity}
    {head : Option (Fin capacity)} {ids : List (Fin capacity)}
    (rep : Represents store head ids) (j : Nat) (hj : j < ids.length) (pos : 0 < j) :
    head ≠ some ids[j] := by
  intro he
  have h0 : 0 < ids.length := by omega
  have eqj : ids[0] = ids[j] := Option.some.inj ((represents_head_zero rep h0).symm.trans he)
  have eqi : 0 = j := rep.1.getElem_inj_iff.mp eqj
  omega

/-- **Correctness of doubly-linked list prepend.** Fix a capacity $n$ and let $s$ be a store
assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Suppose moreover that $s$ with head $\mathrm{head}$
represents a list $L = (\ell_1, \dots, \ell_k)$ of identities, that is, the $\ell_i$ are distinct,
$\mathrm{head}$ is $\ell_1$ (NIL if $k = 0$), and each $s(\ell_i)$ is a node with previous pointer
$\ell_{i-1}$ and next pointer $\ell_{i+1}$ (NIL past the ends of $L$), and that $x$ is not in $L$.
Let $s'$ and $h'$ be the store and head returned by List Prepend on $s$, $\mathrm{head}$ and $x$.
Then $s'$ with head $h'$ represents the list $(x, \ell_1, \dots, \ell_k)$. -/
public theorem listPrepend_represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome)
    (ids : List (Fin capacity)) (rep : Represents store head ids) (fresh : x ∉ ids) :
    Represents (listPrepend store head x hx hh).ret.1
      (listPrepend store head x hx hh).ret.2 (x :: ids) := by
  let access := represents_head_allocated rep
  change Represents (listPrepend store head x hx access).ret.1
    (listPrepend store head x hx access).ret.2 (x :: ids)
  have freshHead : head ≠ some x := fun he => fresh (represents_head_mem rep he)
  rw [listPrepend_head]
  refine ⟨List.nodup_cons.mpr ⟨fresh, rep.1⟩, rfl, ?_⟩
  intro i hi
  cases i with
  | zero =>
    refine ⟨{ (store.get x).get hx with next := head, prev := none }, ?_, rfl, ?_⟩
    · simpa using listPrepend_node store head x hx access freshHead
    · cases ids <;> simpa using rep.2.1
  | succ j =>
    have hj : j < ids.length := by simpa using hi
    obtain ⟨node, hn, hp, hnext⟩ := rep.2.2 j hj
    have xj : x ≠ ids[j] := fun he => fresh (he ▸ List.getElem_mem hj)
    cases j with
    | zero =>
      have he : head = some ids[0] := represents_head_zero rep hj
      refine ⟨{ node with prev := some x }, ?_, rfl, ?_⟩
      · simpa [hn] using listPrepend_oldHead store head x hx access ids[0] he xj
      · simpa using hnext
    | succ j =>
      refine ⟨node, ?_, ?_, ?_⟩
      · simpa using (listPrepend_frame store head x hx access ids[j + 1] xj
          (represents_later_not_head rep (j + 1) hj (by omega))).trans hn
      · simpa using hp
      · simpa [Nat.add_assoc] using hnext

/-- **Doubly-linked list prepend preserves disjoint lists.** Fix a capacity $n$ and let $s$ be a
store assigning to each identity $i < n$ either a node or nothing, let $\mathrm{head}$ be NIL or an
identity, and let $x$ be an identity such that $s(x)$ is a node and, when $\mathrm{head}$ is an
identity, $s(\mathrm{head})$ is a node. Suppose moreover that $s$ with some head $o$ represents a
list $L = (\ell_1, \dots, \ell_k)$ of identities, that is, the $\ell_i$ are distinct, $o$ is
$\ell_1$ (NIL if $k = 0$), and each $s(\ell_i)$ is a node with previous pointer $\ell_{i-1}$ and
next pointer $\ell_{i+1}$ (NIL past the ends of $L$), that $x$ is not in $L$, and that
$\mathrm{head}$ is NIL or an identity not in $L$. Let $s'$ be the store returned by List Prepend on
$s$, $\mathrm{head}$ and $x$. Then $s'$ with head $o$ also represents $L$. -/
public theorem listPrepend_disjoint_represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome)
    (otherHead : Option (Fin capacity)) (otherIds : List (Fin capacity))
    (rep : Represents store otherHead otherIds) (fresh : x ∉ otherIds)
    (disjoint : ∀ h, head = some h → h ∉ otherIds) :
    Represents (listPrepend store head x hx hh).ret.1 otherHead otherIds := by
  refine ⟨rep.1, rep.2.1, ?_⟩
  intro i hi
  obtain ⟨node, hn, hp, hnext⟩ := rep.2.2 i hi
  have xi : x ≠ otherIds[i] := fun he => fresh (he ▸ List.getElem_mem hi)
  have hd : head ≠ some otherIds[i] := fun he => disjoint _ he (List.getElem_mem hi)
  exact ⟨node, (listPrepend_frame store head x hx hh otherIds[i] xi hd).trans hn, hp, hnext⟩

/-- **Uniform cost bound for doubly linked list prepend.** Let a store assign to each identity
below $n$ either nothing or a doubly linked list node, let the head be an identity below $n$ or
NIL, and let $x$ be an identity whose store entry is a node, where the store entry of the head is
also a node when the head is not NIL. Then prepending $x$ costs at most $5$ time units, counting
one unit per pointer assignment and per NIL test of the old head. -/
public theorem listPrepend_time_le {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hh : ∀ h, head = some h → (store.get h).isSome) :
    (listPrepend store head x hx hh).time ≤ 5 := by
  rw [listPrepend_time]
  split <;> decide

end Cslib.Algorithms.Lean.DoublyLinkedList
