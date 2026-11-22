/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Basic

/-!
# Doubly linked list deletion

CLRS fourth edition, section 10.2, printed page 261, `LIST-DELETE`.
The supplied node remains allocated; only its predecessor, successor and header
are spliced. Costs count NIL tests and executed pointer assignments, not physical
RAM accesses, persistent-store copies or native execution time.
-/

namespace Cslib.Algorithms.Lean.DoublyLinkedList

open Cslib.Algorithms.Lean

universe u

private lemma first_write_preserves_x {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x p : Fin capacity)
    (hx : (store.get x).isSome) (hp : (store.get p).isSome) :
    (store.set p.val
      (some { (store.get p).get hp with next := ((store.get x).get hx).next }) p.isLt).get x =
      store.get x := by
  change (store.set p.val
    (some { (store.get p).get hp with next := ((store.get x).get hx).next }) p.isLt)[x.val] =
    store[x.val]
  by_cases hpx : p = x
  · subst p
    rw [Vector.getElem_set]
    simp only [↓reduceIte]
    change some ((store.get x).get hx) = store.get x
    exact Option.some_get hx
  · rw [Vector.getElem_set]
    have hv : p.val ≠ x.val := fun he => hpx (Fin.ext he)
    simp only [hv, ↓reduceIte]

private def finishDelete {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    TimeM Nat (Vector (Option (Node α (Fin capacity))) capacity × Option (Fin capacity)) := do
  let currentX := (store.get x).get hx
  TimeM.tick 1
  match he : currentX.next with
  | none => pure (store, head)
  | some n =>
    let currentN := (store.get n).get (hn n he)
    TimeM.tick 1
    pure (store.set n.val (some { currentN with prev := currentX.prev }) n.isLt, head)

/-- **Deletion from a doubly linked list.** Let the store be an array of cells, each either empty
or holding a node with a payload and optional next and previous pointers to cells, let $h$ be
the optional head pointer, and let $x$ be a cell holding a node such that each cell named by its
previous or next pointer also holds a node. Following CLRS `LIST-DELETE`, deleting $x$ returns a
new store and head as follows. If the node at $x$ has a previous pointer $p$, the next pointer of
the node at $p$ is set to the next pointer of $x$ and the head stays $h$; otherwise the head
becomes the next pointer of $x$. Then, if the node at $x$ has a next pointer $s$, the previous
pointer of the node at $s$ in the store from the first step is set to the previous pointer of $x$.
The computation is charged one unit for each of the two NIL tests and one unit for each executed
pointer or head assignment, so three or four units in total.

The record stored at $x$ is kept and no cell is freed; list consistency is needed only for
correctness, not to run the procedure. -/
public def listDelete {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    TimeM Nat (Vector (Option (Node α (Fin capacity))) capacity × Option (Fin capacity)) := do
  let originalX := (store.get x).get hx
  TimeM.tick 1
  match he : originalX.prev with
  | none =>
    TimeM.tick 1
    finishDelete store originalX.next x hx hn
  | some p =>
    let originalP := (store.get p).get (hp p he)
    TimeM.tick 1
    let store1 := store.set p.val (some { originalP with next := originalX.next }) p.isLt
    have hxeq : store1.get x = store.get x := first_write_preserves_x store x p hx (hp p he)
    have hx1 : (store1.get x).isSome := by rw [hxeq]; exact hx
    have hn1 : ∀ n, ((store1.get x).get hx1).next = some n → (store1.get n).isSome := by
      intro n hnext
      have hn0 : (store.get n).isSome := hn n (by simpa only [hxeq] using hnext)
      change (store.set p.val (some { originalP with next := originalX.next }) p.isLt)[n.val].isSome
      rw [Vector.getElem_set]
      split
      · rfl
      · exact hn0
    finishDelete store1 head x hx1 hn1

private lemma finishDelete_time {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    (finishDelete store head x hx hn).time =
      if ((store.get x).get hx).next.isSome then 2 else 1 := by
  unfold finishDelete
  simp only [TimeM.time_bind, TimeM.time_tick]
  split <;> simp_all

private lemma finishDelete_head {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    (finishDelete store head x hx hn).ret.2 = head := by
  unfold finishDelete
  simp only [TimeM.ret_bind]
  split <;> simp

/-- **Running time of doubly linked list deletion.** Let the store be an array of cells, each
either empty or holding a node with optional next and previous pointers, let $h$ be the optional
head pointer, and let $x$ be a cell holding a node such that each cell named by its previous or
next pointer also holds a node. Counting one unit per NIL test and per executed pointer or head
assignment, deleting $x$ from the list with head $h$ costs exactly $4$ units if the node at $x$
has a next pointer, and exactly $3$ units otherwise. -/
public theorem listDelete_time {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    (listDelete store head x hx hp hn).time =
      if ((store.get x).get hx).next.isSome then 4 else 3 := by
  unfold listDelete
  simp only [TimeM.time_bind, TimeM.time_tick]
  split <;> simp only [TimeM.time_bind, TimeM.time_tick, finishDelete_time]
  · split <;> rfl
  · simp only [first_write_preserves_x]
    split <;> rfl

/-- **Header after doubly linked list deletion.** Let $S$ be a store of $n$ cells, each empty or
holding a node (a payload with next and previous pointers, each an index or NIL), let $h$ be a
header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell holds a node
$X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor $X.\mathrm{next}$
hold nodes whenever these pointers are not NIL. Let $h'$ be the header returned by List Delete on
$S$, $h$ and $x$. Then $h' = h$ if $X.\mathrm{prev}$ is not NIL, and $h' = X.\mathrm{next}$ if
$X.\mathrm{prev}$ is NIL. -/
public theorem listDelete_head {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    (listDelete store head x hx hp hn).ret.2 =
      if ((store.get x).get hx).prev.isSome then head else ((store.get x).get hx).next := by
  unfold listDelete
  simp only [TimeM.ret_bind]
  split <;> simp_all only [TimeM.ret_bind, finishDelete_head,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]

private lemma finishDelete_ret {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    (finishDelete store head x hx hn).ret =
      (match ((store.get x).get hx).next with
       | none => store
       | some n => store.set n.val
           ((store.get n).map fun node => { node with prev := ((store.get x).get hx).prev }) n.isLt,
       head) := by
  unfold finishDelete
  simp only [TimeM.ret_bind]
  split
  · simp_all
  · rename_i n he
    simp only [TimeM.ret_bind, TimeM.ret_pure, he]
    apply congrArg (fun cell => (store.set n.val cell n.isLt, head))
    exact (congrArg (Option.map fun (node : Node α (Fin capacity)) =>
      { node with prev := ((store.get x).get hx).prev }) (Option.some_get (hn n he)))

/-- **Result of doubly linked list deletion.** Let $S$ be a store of $n$ cells, each empty or
holding a node (a payload with next and previous pointers, each an index or NIL), let $h$ be a
header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell holds a node
$X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor $X.\mathrm{next}$
hold nodes whenever these pointers are not NIL. Let $T$ be $S$ if $X.\mathrm{prev}$ is NIL, and
otherwise $S$ with the next pointer of the node in cell $X.\mathrm{prev}$ set to
$X.\mathrm{next}$. Then List Delete on $S$, $h$ and $x$ returns the store equal to $T$ if
$X.\mathrm{next}$ is NIL, and otherwise to $T$ with the previous pointer of the node in cell
$X.\mathrm{next}$ of $T$ set to $X.\mathrm{prev}$, together with the header $h$ if
$X.\mathrm{prev}$ is not NIL and $X.\mathrm{next}$ if it is NIL. The successor's node is read
from $T$, so when $X.\mathrm{prev}$ and $X.\mathrm{next}$ are the same index (not NIL), both
pointer updates apply to its node. -/
public theorem listDelete_ret {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
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
       if originalX.prev.isSome then head else originalX.next) := by
  dsimp only
  unfold listDelete
  simp only [TimeM.ret_bind]
  split
  · rename_i he
    simp only [TimeM.ret_bind, finishDelete_ret, he, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  · rename_i p he
    simp only [TimeM.ret_bind, finishDelete_ret, first_write_preserves_x, he,
      Option.isSome_some, ↓reduceIte]
    have hm := congrArg (Option.map fun (node : Node α (Fin capacity)) =>
      { node with next := ((store.get x).get hx).next }) (Option.some_get (hp p he))
    simp only [Option.map_some] at hm
    simp only [hm]
    rfl

/-- **Cellwise result of doubly linked list deletion.** Let $S$ be a store of $n$ cells, each
empty or holding a node (a payload with next and previous pointers, each an index or NIL), let $h$
be a header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell holds a
node $X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor
$X.\mathrm{next}$ hold nodes whenever these pointers are not NIL. Let $S'$ be the store returned
by List Delete on $S$, $h$ and $x$. For an index $z$, let $C$ be the cell $S(z)$ with the next
pointer of its node set to $X.\mathrm{next}$ if $X.\mathrm{prev} = z$, and $C = S(z)$ otherwise.
Then $S'(z)$ is $C$ with the previous pointer of its node set to $X.\mathrm{prev}$ if
$X.\mathrm{next} = z$, and $S'(z) = C$ otherwise; an empty cell stays empty. So the write at the
predecessor is applied before the write at the successor. -/
public theorem listDelete_get {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (z : Fin capacity) :
    (listDelete store head x hx hp hn).ret.1.get z =
      let originalX := (store.get x).get hx
      let carried := if originalX.prev = some z then
        (store.get z).map fun node => { node with next := originalX.next } else store.get z
      if originalX.next = some z then
        carried.map fun node => { node with prev := originalX.prev } else carried := by
  have getEq (s : Vector (Option (Node α (Fin capacity))) capacity) (i : Fin capacity) :
      s.get i = s[i.val] := rfl
  rw [listDelete_ret]
  simp only [getEq]
  cases hprev : ((store.get x).get hx).prev with
  | none =>
    cases hnext : ((store.get x).get hx).next with
    | none => simp
    | some n =>
      by_cases hnz : n = z <;> (try subst n) <;> simp_all [Fin.ext_iff]
  | some p =>
    cases hnext : ((store.get x).get hx).next with
    | none =>
      by_cases hpz : p = z <;> (try subst p) <;> simp_all [Fin.ext_iff]
    | some n =>
      by_cases hpz : p = z <;> by_cases hnz : n = z <;>
        (try subst p) <;> (try subst n) <;> simp_all [Fin.ext_iff]

/-- **Deletion changes only the cells of the neighbors.** Let $S$ be a store of $n$ cells, each
empty or holding a node (a payload with next and previous pointers, each an index or NIL), let $h$
be a header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell holds a
node $X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor
$X.\mathrm{next}$ hold nodes whenever these pointers are not NIL. Let $S'$ be the store returned
by List Delete on $S$, $h$ and $x$. Then $S'(z) = S(z)$ for every index $z$ with
$X.\mathrm{prev} \ne z$ and $X.\mathrm{next} \ne z$. -/
public theorem listDelete_frame {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (z : Fin capacity)
    (hzp : ((store.get x).get hx).prev ≠ some z)
    (hzn : ((store.get x).get hx).next ≠ some z) :
    (listDelete store head x hx hp hn).ret.1.get z = store.get z := by
  rw [listDelete_get]
  simp only [hzp, hzn, ↓reduceIte]

/-- **Deletion from a doubly linked list allocates and frees nothing.** Let $S$ be a store of $n$
cells, each empty or holding a node (a payload with next and previous pointers, each an index or
NIL), let $h$ be a header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose
cell holds a node $X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor
$X.\mathrm{next}$ hold nodes whenever these pointers are not NIL. Let $S'$ be the store returned
by List Delete on $S$, $h$ and $x$. Then for every index $z$, the cell $S'(z)$ holds a node if and
only if $S(z)$ does. -/
public theorem listDelete_allocated {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (z : Fin capacity) :
    ((listDelete store head x hx hp hn).ret.1.get z).isSome = (store.get z).isSome := by
  rw [listDelete_get]
  by_cases hpz : ((store.get x).get hx).prev = some z <;>
    by_cases hnz : ((store.get x).get hx).next = some z <;> simp [hpz, hnz]

/-- **Deletion preserves payloads.** Let $S$ be a store of $n$ cells, each empty or holding a node
(a payload with next and previous pointers, each an index or NIL), let $h$ be a header (an index
in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell holds a node $X$ such that the
cells at the predecessor $X.\mathrm{prev}$ and the successor $X.\mathrm{next}$ hold nodes
whenever these pointers are not NIL. Let $S'$ be the store returned by List Delete on $S$, $h$
and $x$. Then for every index $z$, either $S'(z)$ and $S(z)$ are both empty, or both hold nodes
and these two nodes have the same payload. -/
public theorem listDelete_payload {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (z : Fin capacity) :
    ((listDelete store head x hx hp hn).ret.1.get z).map Node.payload =
      (store.get z).map Node.payload := by
  rw [listDelete_get]
  by_cases hpz : ((store.get x).get hx).prev = some z <;>
    by_cases hnz : ((store.get x).get hx).next = some z <;>
    simp [hpz, hnz, Option.map_map, Function.comp_def]

/-- **The deleted node keeps its record.** Let $S$ be a store of $n$ cells, each empty or holding
a node (a payload with next and previous pointers, each an index or NIL), let $h$ be a header (an
index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell holds a node $X$ such that
the cells at the predecessor $X.\mathrm{prev}$ and the successor $X.\mathrm{next}$ hold nodes
whenever these pointers are not NIL. Let $S'$ be the store returned by List Delete on $S$, $h$
and $x$. Then $S'(x) = S(x)$: the deleted node stays allocated with its payload and both of its
pointers unchanged. -/
public theorem listDelete_deleted_record {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    (listDelete store head x hx hp hn).ret.1.get x = store.get x := by
  rw [listDelete_get]
  generalize hnode : (store.get x).get hx = node
  have ho : store.get x = some node :=
    (Option.some_get hx).symm.trans (congrArg some hnode)
  rcases node with ⟨payload, next, prev⟩
  by_cases hpz : prev = some x <;>
    by_cases hnz : next = some x <;>
    simp [hpz, hnz, ho]

/-- **Deletion preserves lists avoiding the deleted node's neighbors.** Let $S$ be a store of $n$
cells, each empty or holding a node (a payload with next and previous pointers, each an index or
NIL), let $h$ be a header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose
cell holds a node $X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor
$X.\mathrm{next}$ hold nodes whenever these pointers are not NIL. Let $S'$ be the store returned
by List Delete on $S$, $h$ and $x$. Let $h_0$ be a header and $L$ a list of indices such that $S$
with header $h_0$ represents $L$: the entries of $L$ are distinct, $h_0$ is the first entry of
$L$ (NIL if $L$ is empty), and the cell of each entry of $L$ holds a node whose previous and next
pointers are the adjacent entries of $L$, NIL at the ends. If neither $X.\mathrm{prev}$ nor
$X.\mathrm{next}$ is an entry of $L$, then $S'$ with header $h_0$ also represents $L$. -/
public theorem listDelete_disjoint_represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (otherHead : Option (Fin capacity)) (otherIds : List (Fin capacity))
    (rep : Represents store otherHead otherIds)
    (disjointP : ∀ p, ((store.get x).get hx).prev = some p → p ∉ otherIds)
    (disjointN : ∀ n, ((store.get x).get hx).next = some n → n ∉ otherIds) :
    Represents (listDelete store head x hx hp hn).ret.1 otherHead otherIds := by
  refine ⟨rep.1, rep.2.1, ?_⟩
  intro i hi
  obtain ⟨node, hcell, hprev, hnext⟩ := rep.2.2 i hi
  have hpz : ((store.get x).get hx).prev ≠ some otherIds[i] :=
    fun he => disjointP _ he (List.getElem_mem hi)
  have hnz : ((store.get x).get hx).next ≠ some otherIds[i] :=
    fun he => disjointN _ he (List.getElem_mem hi)
  exact ⟨node, (listDelete_frame store head x hx hp hn _ hpz hnz).trans hcell,
    hprev, hnext⟩

/-- **Doubly linked list deletion costs at most four events.** Let $S$ be a store of $n$ cells,
each empty or holding a node (a payload with next and previous pointers, each an index or NIL),
let $h$ be a header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell
holds a node $X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor
$X.\mathrm{next}$ hold nodes whenever these pointers are not NIL. Then List Delete on $S$, $h$
and $x$ costs at most $4$, counting NIL tests and executed pointer and header assignments. -/
public theorem listDelete_time_le {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    (listDelete store head x hx hp hn).time ≤ 4 := by
  rw [listDelete_time]
  split <;> decide

private lemma optional_index_eq {ι : Type u} {ids : List ι} (nd : ids.Nodup)
    (i j : Nat) (hj : j < ids.length) : ids[i]? = some ids[j] ↔ i = j := by
  constructor
  · intro he
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp he
    exact nd.getElem_inj_iff.mp he
  · intro he
    subst i
    exact List.getElem?_eq_getElem hj

private lemma previous_index_eq {ι : Type u} {ids : List ι} (nd : ids.Nodup)
    (k j : Nat) (hj : j < ids.length) :
    (if k = 0 then none else ids[k - 1]?) = some ids[j] ↔ 0 < k ∧ k - 1 = j := by
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk, optional_index_eq nd (k - 1) j hj, Nat.pos_of_ne_zero hk]

private lemma represents_selected {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity))
    (rep : Represents store head ids) (k : Nat) (hk : k < ids.length)
    (hx : (store.get ids[k]).isSome) :
    ((store.get ids[k]).get hx).prev = (if k = 0 then none else ids[k - 1]?) ∧
      ((store.get ids[k]).get hx).next = ids[k + 1]? := by
  obtain ⟨node, he, hp, hn⟩ := rep.2.2 k hk
  simpa only [he, Option.get_some] using And.intro hp hn

private lemma delete_indexed_cell {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity))
    (rep : Represents store head ids) (k : Nat) (hk : k < ids.length)
    (hx : (store.get ids[k]).isSome)
    (hp : ∀ p, ((store.get ids[k]).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get ids[k]).get hx).next = some n → (store.get n).isSome)
    (j : Nat) (hj : j < ids.length) (node : Node α (Fin capacity))
    (hcell : store.get ids[j] = some node) :
    (listDelete store head ids[k] hx hp hn).ret.1.get ids[j] =
      some { node with
        next := if 0 < k ∧ k - 1 = j then ids[k + 1]? else node.next,
        prev := if k + 1 = j then (if k = 0 then none else ids[k - 1]?) else node.prev } := by
  have sel := represents_selected store head ids rep k hk hx
  rw [listDelete_get]
  simp only [sel.1, sel.2, previous_index_eq rep.1 k j hj,
    optional_index_eq rep.1 (k + 1) j hj, hcell]
  by_cases hpj : 0 < k ∧ k - 1 = j <;> by_cases hnj : k + 1 = j <;>
    simp [hpj, hnj]

private lemma delete_indexed_head {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity))
    (rep : Represents store head ids) (k : Nat) (hk : k < ids.length)
    (hx : (store.get ids[k]).isSome)
    (hp : ∀ p, ((store.get ids[k]).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get ids[k]).get hx).next = some n → (store.get n).isSome) :
    (listDelete store head ids[k] hx hp hn).ret.2 = (ids.eraseIdx k).head? := by
  have sel := represents_selected store head ids rep k hk hx
  rw [listDelete_head, sel.1, sel.2, List.head?_eq_getElem?, List.getElem?_eraseIdx]
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkm : k - 1 < ids.length := by omega
    simp [hk0, List.getElem?_eq_getElem hkm, rep.2.1,
      List.head?_eq_getElem?, Nat.pos_of_ne_zero hk0]

private lemma delete_indexed_represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (ids : List (Fin capacity))
    (rep : Represents store head ids) (k : Nat) (hk : k < ids.length)
    (hx : (store.get ids[k]).isSome)
    (hp : ∀ p, ((store.get ids[k]).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get ids[k]).get hx).next = some n → (store.get n).isSome) :
    Represents (listDelete store head ids[k] hx hp hn).ret.1
      (listDelete store head ids[k] hx hp hn).ret.2 (ids.eraseIdx k) := by
  refine ⟨rep.1.eraseIdx k, delete_indexed_head store head ids rep k hk hx hp hn, ?_⟩
  intro i hi
  have hlen := List.length_eraseIdx_of_lt hk
  by_cases before : i < k
  · have old : i < ids.length := by omega
    obtain ⟨node, hcell, hpold, hnold⟩ := rep.2.2 i old
    let updated : Node α (Fin capacity) := { node with
      next := if 0 < k ∧ k - 1 = i then ids[k + 1]? else node.next,
      prev := if k + 1 = i then (if k = 0 then none else ids[k - 1]?) else node.prev }
    refine ⟨updated, ?_, ?_, ?_⟩
    · rw [List.getElem_eraseIdx]
      simp only [dite_eq_left before]
      exact delete_indexed_cell store head ids rep k hk hx hp hn i old node hcell
    · change (if k + 1 = i then (if k = 0 then none else ids[k - 1]?) else node.prev) =
        if i = 0 then none else (ids.eraseIdx k)[i - 1]?
      have kn : k + 1 ≠ i := by omega
      rw [ite_eq_right kn, hpold]
      by_cases iz : i = 0
      · simp [iz]
      · have im : i - 1 < k := by omega
        simp [iz, List.getElem?_eraseIdx, im]
    · change (if 0 < k ∧ k - 1 = i then ids[k + 1]? else node.next) =
        (ids.eraseIdx k)[i + 1]?
      by_cases near : i + 1 = k
      · have hpnear : 0 < k ∧ k - 1 = i := by omega
        have hnot : ¬i + 1 < k := by omega
        have he : i + 1 + 1 = k + 1 := by omega
        simp [hpnear, List.getElem?_eraseIdx, hnot, he]
      · have hpnear : ¬(0 < k ∧ k - 1 = i) := by omega
        have hlt : i + 1 < k := by omega
        simp [hpnear, hnold, List.getElem?_eraseIdx, hlt]
  · have after : k ≤ i := by omega
    have old : i + 1 < ids.length := by omega
    obtain ⟨node, hcell, hpold, hnold⟩ := rep.2.2 (i + 1) old
    let updated : Node α (Fin capacity) := { node with
      next := if 0 < k ∧ k - 1 = i + 1 then ids[k + 1]? else node.next,
      prev := if k + 1 = i + 1 then (if k = 0 then none else ids[k - 1]?) else node.prev }
    refine ⟨updated, ?_, ?_, ?_⟩
    · rw [List.getElem_eraseIdx]
      simp only [dite_eq_right before]
      exact delete_indexed_cell store head ids rep k hk hx hp hn (i + 1) old node hcell
    · change (if k + 1 = i + 1 then (if k = 0 then none else ids[k - 1]?) else node.prev) =
        if i = 0 then none else (ids.eraseIdx k)[i - 1]?
      by_cases near : i = k
      · subst i
        by_cases kz : k = 0
        · simp [kz]
        · have km : k - 1 < k := by omega
          simp [kz, List.getElem?_eraseIdx, km]
      · have kne : k + 1 ≠ i + 1 := by omega
        have iz : i ≠ 0 := by omega
        have im : k ≤ i - 1 := by omega
        rw [ite_eq_right kne, hpold]
        have ie : i - 1 + 1 = i := by omega
        simp [iz, List.getElem?_eraseIdx, Nat.not_lt.mpr im, ie]
    · change (if 0 < k ∧ k - 1 = i + 1 then ids[k + 1]? else node.next) =
        (ids.eraseIdx k)[i + 1]?
      have kn : ¬(0 < k ∧ k - 1 = i + 1) := by omega
      have hi1 : k ≤ i + 1 := by omega
      rw [ite_eq_right kn, hnold]
      simp only [List.getElem?_eraseIdx, ite_eq_right (Nat.not_lt.mpr hi1)]

/-- **Correctness of doubly linked list deletion.** Let $S$ be a store of $n$ cells, each empty or
holding a node (a payload with next and previous pointers, each an index or NIL), let $h$ be a
header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell holds a node
$X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor $X.\mathrm{next}$
hold nodes whenever these pointers are not NIL. Let $S'$ and $h'$ be the store and header
returned by List Delete on $S$, $h$ and $x$. Let $L$ be a list of indices such that $S$ with
header $h$ represents $L$: the entries of $L$ are distinct, $h$ is the first entry of $L$ (NIL if
$L$ is empty), and the cell of each entry of $L$ holds a node whose previous and next pointers
are the adjacent entries of $L$, NIL at the ends. If $x$ is an entry of $L$, then $S'$ with
header $h'$ represents the list obtained from $L$ by removing $x$. -/
public theorem listDelete_represents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (head : Option (Fin capacity)) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hn : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (ids : List (Fin capacity)) (rep : Represents store head ids) (member : x ∈ ids) :
    Represents (listDelete store head x hx hp hn).ret.1
      (listDelete store head x hx hp hn).ret.2 (ids.erase x) := by
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem member
  subst x
  rw [rep.1.erase_getElem k hk]
  exact delete_indexed_represents store head ids rep k hk hx hp hn

end Cslib.Algorithms.Lean.DoublyLinkedList
