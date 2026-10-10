/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Sentinel.Basic

import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Delete
import Mathlib.Data.List.Chain

/-!
# Deletion from a circular doubly-linked list with a sentinel

CLRS fourth edition, section 10.2, printed page 262, LIST-DELETE-prime.
The actual computation performs both pointer assignments in source order and
rereads the successor from the carried store. The selected record stays allocated.
Allocation access is the execution domain; sentinel exclusion and list membership
are representation-proof premises, not new runtime guards.

The same canonical TimeM computation counts exactly two pointer assignments, even
for access-valid aliases. This metric excludes physical RAM accesses, persistent
store copying, allocation, bit cost, space and native execution time.

Private proof support relates the exact circular predicate to List.IsChain and
reuses canonical listDelete field laws through an exact return bridge. The actual
executor does not call listDelete. Generic erasure is ids.erase x and disjointness
includes both sentinels in their corresponding address lists.
-/

public section

namespace Cslib.Algorithms.Lean.DoublyLinkedList

open Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

private lemma get_set {α : Type u} {n : Nat} (xs : Vector α n)
    (i j : Fin n) (a : α) :
    (xs.set i.val a i.isLt).get j = if i = j then a else xs.get j := by
  change (xs.set i.val a i.isLt)[j.val] = if i = j then a else xs[j.val]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff]

private lemma first_write_keeps_x {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x p : Fin n)
    (nx np : Node α (Fin n))
    (hx : store.get x = some nx) (hp : store.get p = some np) :
    (store.set p.val (some { np with next := nx.next }) p.isLt).get x = some nx := by
  rw [get_set]
  by_cases hpx : p = x
  · subst p
    have hnp : nx = np := Option.some.inj (hx.symm.trans hp)
    subst np
    simp only [ite_true]
  · simpa only [hpx, ite_false] using hx

/-- Both sentinel deletion assignments, with dereference validity only. -/
public def sentinelDelete {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ((store.get x).get hx).prev.isSome)
    (hn : ((store.get x).get hx).next.isSome)
    (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    TimeM Nat (Vector (Option (Node α (Fin capacity))) capacity) := do
  let nx := (store.get x).get hx
  let p := nx.prev.get hp
  have hpAllocated := hprev p (Option.some_get hp).symm
  let currentP := (store.get p).get hpAllocated
  TimeM.tick 1
  let updatedP := { currentP with next := nx.next }
  let store1 := store.set p.val (some updatedP) p.isLt
  have hStable : store1.get x = some nx :=
    first_write_keeps_x store x p nx currentP
      (Option.some_get hx).symm (Option.some_get hpAllocated).symm
  have hx1 : (store1.get x).isSome := by
    rw [hStable]
    rfl
  let currentX := (store1.get x).get hx1
  have currentX_eq : currentX = nx :=
    Option.some.inj ((Option.some_get hx1).trans hStable)
  have hn1 : currentX.next.isSome := by
    rw [currentX_eq]
    exact hn
  let n := currentX.next.get hn1
  have hNext : nx.next = some n := by
    rw [← currentX_eq]
    exact (Option.some_get hn1).symm
  have hnAllocated : (store1.get n).isSome := by
    dsimp only [store1]
    rw [get_set]
    split
    · rfl
    · exact hnext n hNext
  let currentN := (store1.get n).get hnAllocated
  TimeM.tick 1
  pure (store1.set n.val (some { currentN with prev := currentX.prev }) n.isLt)

/-- Exactly two pointer assignments, including access-valid alias cases. -/
public theorem sentinelDelete_time {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ((store.get x).get hx).prev.isSome)
    (hn : ((store.get x).get hx).next.isSome)
    (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    (sentinelDelete store x hx hp hn hprev hnext).time = 2 := by
  simp [sentinelDelete]

/-- The two carried record updates determine the complete returned store. -/
public theorem sentinelDelete_ret {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ((store.get x).get hx).prev.isSome)
    (hn : ((store.get x).get hx).next.isSome)
    (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    let nx := (store.get x).get hx
    let p := nx.prev.get hp
    let n := nx.next.get hn
    let carried := store.set p.val
      ((store.get p).map fun node => { node with next := nx.next }) p.isLt
    (sentinelDelete store x hx hp hn hprev hnext).ret =
      carried.set n.val ((carried.get n).map fun node => { node with prev := nx.prev }) n.isLt := by
  cases hpv : ((store.get x).get hx).prev with
  | none => simp [hpv] at hp
  | some p =>
    cases hnv : ((store.get x).get hx).next with
    | none => simp [hnv] at hn
    | some n =>
      have hpa := hprev p hpv
      let np := (store.get p).get hpa
      let carried := store.set p.val (some { np with next := some n }) p.isLt
      have stable : carried.get x = some ((store.get x).get hx) := by
        simpa only [carried, np, hnv] using
          first_write_keeps_x store x p ((store.get x).get hx) ((store.get p).get hpa)
            (Option.some_get hx).symm (Option.some_get hpa).symm
      have hna : (carried.get n).isSome := by
        dsimp only [carried]
        rw [get_set]
        split
        · rfl
        · exact hnext n hnv
      have pm : (store.get p).map (fun node => { node with next := some n }) =
          some { np with next := some n } := by
        exact (congrArg (Option.map fun node => { node with next := some n })
          (Option.some_get hpa)).symm
      have nm : (carried.get n).map (fun node => { node with prev := some p }) =
          some { (carried.get n).get hna with prev := some p } := by
        exact (congrArg (Option.map fun node => { node with prev := some p })
          (Option.some_get hna)).symm
      simp only [sentinelDelete, TimeM.ret_bind, TimeM.ret_pure, hpv, hnv,
        Option.get_some, pm]
      change carried.set _ _ _ = carried.set _ _ _
      simp only [carried, np] at stable
      simp only [stable, Option.get_some, hpv, hnv]
      change carried.set n.val
        (some { (carried.get n).get hna with prev := some p }) n.isLt =
        carried.set n.val ((carried.get n).map fun node => { node with prev := some p }) n.isLt
      rw [nm]

private lemma sentinelDelete_ret_eq_listDelete {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ((store.get x).get hx).prev.isSome)
    (hn : ((store.get x).get hx).next.isSome)
    (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome) :
    (sentinelDelete store x hx hp hn hprev hnext).ret =
      (listDelete store none x hx hprev hnext).ret.1 := by
  cases hpv : ((store.get x).get hx).prev with
  | none => simp [hpv] at hp
  | some p =>
    cases hnv : ((store.get x).get hx).next with
    | none => simp [hnv] at hn
    | some n =>
      rw [sentinelDelete_ret, listDelete_ret]
      simp only [hpv, hnv, Option.get_some]

section

variable {α : Type u} {capacity : Nat}
  (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
  (hx : (store.get x).isSome)
  (hp : ((store.get x).get hx).prev.isSome)
  (hn : ((store.get x).get hx).next.isSome)
  (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
  (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)

/-- Every returned cell follows the predecessor write and then the carried successor write. -/
public theorem sentinelDelete_get (z : Fin capacity) :
    (sentinelDelete store x hx hp hn hprev hnext).ret.get z =
      let nx := (store.get x).get hx
      let carried := if nx.prev = some z then
        (store.get z).map fun node => { node with next := nx.next } else store.get z
      if nx.next = some z then
        carried.map fun node => { node with prev := nx.prev } else carried := by
  rw [sentinelDelete_ret_eq_listDelete]
  exact listDelete_get store none x hx hprev hnext z

/-- Every complete cell outside the two updated neighbors is unchanged. -/
public theorem sentinelDelete_frame (z : Fin capacity)
    (hzp : ((store.get x).get hx).prev ≠ some z)
    (hzn : ((store.get x).get hx).next ≠ some z) :
    (sentinelDelete store x hx hp hn hprev hnext).ret.get z = store.get z := by
  rw [sentinelDelete_ret_eq_listDelete]
  exact listDelete_frame store none x hx hprev hnext z hzp hzn

/-- Both writes preserve the allocation status at every address. -/
public theorem sentinelDelete_allocated (z : Fin capacity) :
    ((sentinelDelete store x hx hp hn hprev hnext).ret.get z).isSome =
      (store.get z).isSome := by
  rw [sentinelDelete_ret_eq_listDelete]
  exact listDelete_allocated store none x hx hprev hnext z

/-- Every payload, including keys and satellite data, is preserved. -/
public theorem sentinelDelete_payload (z : Fin capacity) :
    ((sentinelDelete store x hx hp hn hprev hnext).ret.get z).map Node.payload =
      (store.get z).map Node.payload := by
  rw [sentinelDelete_ret_eq_listDelete]
  exact listDelete_payload store none x hx hprev hnext z

/-- Unlinking retains the complete selected record. -/
public theorem sentinelDelete_deleted_record :
    (sentinelDelete store x hx hp hn hprev hnext).ret.get x = store.get x := by
  rw [sentinelDelete_ret_eq_listDelete]
  exact listDelete_deleted_record store none x hx hprev hnext

end

private lemma headD_mem_cons {α : Type u} (s : α) (ids : List α) :
    ids.headD s ∈ s :: ids := by
  cases ids <;> simp

private lemma sentinelDelete_disjoint_neighbors {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ((store.get x).get hx).prev.isSome)
    (hn : ((store.get x).get hx).next.isSome)
    (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (t : Fin capacity) (otherIds : List (Fin capacity))
    (rep : CircularRepresents store t otherIds)
    (disjointP : ∀ p, ((store.get x).get hx).prev = some p → p ∉ t :: otherIds)
    (disjointN : ∀ n, ((store.get x).get hx).next = some n → n ∉ t :: otherIds) :
    CircularRepresents (sentinelDelete store x hx hp hn hprev hnext).ret t otherIds := by
  have frame (z : Fin capacity) (hz : z ∈ t :: otherIds) :
      (sentinelDelete store x hx hp hn hprev hnext).ret.get z = store.get z := by
    apply sentinelDelete_frame
    · exact fun he => disjointP z he hz
    · exact fun he => disjointN z he hz
  refine ⟨rep.1, rep.2.1, ?_, ?_⟩
  · obtain ⟨sentinel, hs, hsn, hsp⟩ := rep.2.2.1
    exact ⟨sentinel, (frame t (by simp)).trans hs, hsn, hsp⟩
  · intro before a after he
    obtain ⟨node, ha, hap, han⟩ := rep.2.2.2 before a after he
    have member : a ∈ t :: otherIds := by
      rw [he]
      simp
    exact ⟨node, (frame a member).trans ha, hap, han⟩

private lemma chain_splice {α : Type u} {R S : α → α → Prop}
    {before after : List α} {x : α}
    (h : List.IsChain R (before ++ x :: after))
    (hbefore : x ∉ before) (hafter : x ∉ after)
    (stable : ∀ a b, a ≠ x → b ≠ x → R a b → S a b)
    (join : ∀ a b, R a x → R x b → S a b) :
    List.IsChain S (before ++ after) := by
  have parts := List.isChain_append.mp h
  have tailParts := List.isChain_append.mp
    (show List.IsChain R ([x] ++ after) from parts.2.1)
  have left : List.IsChain S before := parts.1.imp_of_mem_imp fun a b ha hb hab =>
    stable a b (fun heq => hbefore (heq ▸ ha)) (fun heq => hbefore (heq ▸ hb)) hab
  have right : List.IsChain S after := tailParts.2.1.imp_of_mem_imp fun a b ha hb hab =>
    stable a b (fun heq => hafter (heq ▸ ha)) (fun heq => hafter (heq ▸ hb)) hab
  apply left.append right
  intro a ha b hb
  exact join a b (parts.2.2 a ha x (by simp)) (tailParts.2.2 x (by simp) b hb)

private def circleEdge {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (a b : Fin capacity) : Prop :=
  ∃ na nb, store.get a = some na ∧ store.get b = some nb ∧
    na.next = some b ∧ nb.prev = some a

private def segmentRepresents {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (p : Fin capacity) (ids : List (Fin capacity)) (n : Fin capacity) : Prop :=
  (∃ node, store.get p = some node ∧ node.next = some (ids.headD n)) ∧
  (∃ node, store.get n = some node ∧ node.prev = some (ids.getLastD p)) ∧
  ∀ before a after, ids = before ++ a :: after →
    ∃ node, store.get a = some node ∧ node.prev = some (before.getLastD p) ∧
      node.next = some (after.headD n)

private lemma segment_cons {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (p a n : Fin capacity) (ids : List (Fin capacity)) :
    segmentRepresents store p (a :: ids) n ↔
      circleEdge store p a ∧ segmentRepresents store a ids n := by
  constructor
  · rintro ⟨⟨np, hnp, hp⟩, ⟨nn, hnn, hn⟩, nodes⟩
    obtain ⟨na, hna, hap, han⟩ := nodes [] a ids rfl
    refine ⟨⟨np, na, hnp, hna, hp, hap⟩, ⟨na, hna, han⟩,
      ⟨nn, hnn, ?_⟩, ?_⟩
    · simpa only [List.getLastD_cons] using hn
    · intro before b after hsplit
      obtain ⟨node, hnode, hprev, hnext⟩ := nodes (a :: before) b after
        (by simpa only [List.cons_append] using congrArg (List.cons a) hsplit)
      exact ⟨node, hnode, by simpa only [List.getLastD_cons] using hprev, hnext⟩
  · rintro ⟨⟨np, na, hnp, hna, hp, hap⟩,
      ⟨na', hna', han⟩, ⟨nn, hnn, hn⟩, nodes⟩
    have hnaEq : na = na' := Option.some.inj (hna.symm.trans hna')
    subst na'
    refine ⟨⟨np, hnp, hp⟩, ⟨nn, hnn, ?_⟩, ?_⟩
    · simpa only [List.getLastD_cons] using hn
    · intro before b after hsplit
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hsplit
          obtain ⟨rfl, rfl⟩ := hsplit
          exact ⟨na, hna, hap, han⟩
      | cons c before =>
          simp only [List.cons_append, List.cons.injEq] at hsplit
          obtain ⟨rfl, hsplit⟩ := hsplit
          obtain ⟨node, hnode, hprev, hnext⟩ := nodes before b after hsplit
          exact ⟨node, hnode, by simpa only [List.getLastD_cons] using hprev, hnext⟩

private lemma segment_chain {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (p n : Fin capacity) (ids : List (Fin capacity)) :
    segmentRepresents store p ids n ↔ List.IsChain (circleEdge store) (p :: ids ++ [n]) := by
  induction ids generalizing p with
  | nil =>
      change segmentRepresents store p [] n ↔
        List.IsChain (circleEdge store) (p :: n :: [])
      rw [List.isChain_cons_cons]
      simp only [List.isChain_singleton, and_true]
      constructor
      · rintro ⟨⟨np, hnp, hp⟩, ⟨nn, hnn, hn⟩, _⟩
        exact ⟨np, nn, hnp, hnn, hp, hn⟩
      · rintro ⟨np, nn, hnp, hnn, hp, hn⟩
        refine ⟨⟨np, hnp, hp⟩, ⟨nn, hnn, hn⟩, ?_⟩
        intro before a after hsplit
        have : False := by simpa using congrArg List.length hsplit
        exact this.elim
  | cons a ids ih =>
      rw [segment_cons]
      change circleEdge store p a ∧ segmentRepresents store a ids n ↔
        List.IsChain (circleEdge store) (p :: a :: (ids ++ [n]))
      rw [List.isChain_cons_cons, ih]
      rfl

private lemma circular_chain {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (s : Fin capacity) (ids : List (Fin capacity)) :
    CircularRepresents store s ids ↔
      ids.Nodup ∧ s ∉ ids ∧ List.IsChain (circleEdge store) (s :: ids ++ [s]) := by
  rw [← segment_chain]
  constructor
  · rintro ⟨hnd, hs, ⟨node, hnode, hn, hp⟩, nodes⟩
    exact ⟨hnd, hs, ⟨node, hnode, hn⟩, ⟨node, hnode, hp⟩, nodes⟩
  · rintro ⟨hnd, hs, ⟨node, hnode, hn⟩, ⟨node', hnode', hp⟩, nodes⟩
    have hEq : node = node' := Option.some.inj (hnode.symm.trans hnode')
    subst node'
    exact ⟨hnd, hs, ⟨node, hnode, hn, hp⟩, nodes⟩

private lemma edge_iff_links {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (a b : Fin capacity) :
    circleEdge store a b ↔
      (store.get a).map Node.next = some (some b) ∧
      (store.get b).map Node.prev = some (some a) := by
  constructor
  · rintro ⟨na, nb, ha, hb, hn, hp⟩
    simp [ha, hb, hn, hp]
  · cases ha : store.get a <;> cases hb : store.get b <;> simp [ha, hb, circleEdge]

private lemma returned_next {α : Type u} {capacity : Nat}
  (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
  (hx : (store.get x).isSome)
  (hp : ((store.get x).get hx).prev.isSome)
  (hn : ((store.get x).get hx).next.isSome)
  (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
  (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
  (z : Fin capacity) :
    ((sentinelDelete store x hx hp hn hprev hnext).ret.get z).map
      (fun node : Node α (Fin capacity) => node.next) =
      if ((store.get x).get hx).prev = some z then
        (store.get z).map (fun _ => ((store.get x).get hx).next)
      else (store.get z).map (fun node : Node α (Fin capacity) => node.next) := by
  rw [sentinelDelete_get store x hx hp hn hprev hnext z]
  dsimp only
  by_cases hzp : ((store.get x).get hx).prev = some z <;>
    by_cases hzn : ((store.get x).get hx).next = some z <;>
    simp only [hzp, hzn, ite_true, ite_false] <;> cases store.get z <;> rfl

private lemma returned_prev {α : Type u} {capacity : Nat}
  (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
  (hx : (store.get x).isSome)
  (hp : ((store.get x).get hx).prev.isSome)
  (hn : ((store.get x).get hx).next.isSome)
  (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
  (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
  (z : Fin capacity) :
    ((sentinelDelete store x hx hp hn hprev hnext).ret.get z).map
      (fun node : Node α (Fin capacity) => node.prev) =
      if ((store.get x).get hx).next = some z then
        (store.get z).map (fun _ => ((store.get x).get hx).prev)
      else (store.get z).map (fun node : Node α (Fin capacity) => node.prev) := by
  rw [sentinelDelete_get store x hx hp hn hprev hnext z]
  dsimp only
  by_cases hzp : ((store.get x).get hx).prev = some z <;>
    by_cases hzn : ((store.get x).get hx).next = some z <;>
    simp only [hzp, hzn, ite_true, ite_false] <;> cases store.get z <;> rfl

private lemma selected_edges {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (s x : Fin capacity) (before after : List (Fin capacity))
    (h : List.IsChain (circleEdge store) (s :: (before ++ x :: after) ++ [s])) :
    circleEdge store (before.getLastD s) x ∧ circleEdge store x (after.headD s) := by
  have parts := List.isChain_append.mp
    (show List.IsChain (circleEdge store) ((s :: before) ++ x :: (after ++ [s])) from
      by simpa only [List.cons_append, List.append_assoc] using h)
  constructor
  · exact parts.2.2 (before.getLastD s)
      (by simp [List.getLast?_cons, List.getLastD_eq_getLast?]) x (by simp)
  · exact (List.isChain_cons.mp parts.2.1).1 (after.headD s)
      (by cases after <;> simp [List.headD])

private lemma edge_transport {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x p n : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ((store.get x).get hx).prev.isSome)
    (hn : ((store.get x).get hx).next.isSome)
    (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (pred : circleEdge store p x) (succ : circleEdge store x n) :
    (∀ a b, a ≠ x → b ≠ x → circleEdge store a b →
      circleEdge (sentinelDelete store x hx hp hn hprev hnext).ret a b) ∧
    (∀ a b, circleEdge store a x → circleEdge store x b →
      circleEdge (sentinelDelete store x hx hp hn hprev hnext).ret a b) := by
  have predLinks := (edge_iff_links store p x).mp pred
  have succLinks := (edge_iff_links store x n).mp succ
  have hpv : ((store.get x).get hx).prev = some p := by
    apply Option.some.inj
    calc
      some ((store.get x).get hx).prev = (store.get x).map Node.prev :=
        congrArg (fun o => o.map Node.prev) (Option.some_get hx)
      _ = some (some p) := predLinks.2
  have hnv : ((store.get x).get hx).next = some n := by
    apply Option.some.inj
    calc
      some ((store.get x).get hx).next = (store.get x).map Node.next :=
        congrArg (fun o => o.map Node.next) (Option.some_get hx)
      _ = some (some n) := succLinks.1
  constructor
  · intro a b ha hb hab
    have links := (edge_iff_links store a b).mp hab
    have hpa : ((store.get x).get hx).prev ≠ some a := by
      intro he
      have hEq : p = a := Option.some.inj (hpv.symm.trans he)
      subst p
      exact hb (Option.some.inj (Option.some.inj (links.1.symm.trans predLinks.1)))
    have hnb : ((store.get x).get hx).next ≠ some b := by
      intro he
      have hEq : n = b := Option.some.inj (hnv.symm.trans he)
      subst n
      exact ha (Option.some.inj (Option.some.inj (links.2.symm.trans succLinks.2)))
    apply (edge_iff_links _ a b).mpr
    constructor
    · rw [returned_next store x hx hp hn hprev hnext a]
      simp only [hpa, ite_false]
      exact links.1
    · rw [returned_prev store x hx hp hn hprev hnext b]
      simp only [hnb, ite_false]
      exact links.2
  · intro a b hax hxb
    have axLinks := (edge_iff_links store a x).mp hax
    have xbLinks := (edge_iff_links store x b).mp hxb
    have hap : a = p := Option.some.inj (Option.some.inj
      (axLinks.2.symm.trans predLinks.2))
    have hbn : b = n := Option.some.inj (Option.some.inj
      (xbLinks.1.symm.trans succLinks.1))
    subst a
    subst b
    obtain ⟨np, nx, hgetp, hgetx, _, _⟩ := pred
    obtain ⟨nx', nn, hgetx', hgetn, _, _⟩ := succ
    apply (edge_iff_links _ p n).mpr
    constructor
    · rw [returned_next store x hx hp hn hprev hnext p]
      simp only [hpv, hnv, ite_true, hgetp, Option.map_some]
    · rw [returned_prev store x hx hp hn hprev hnext n]
      simp only [hpv, hnv, ite_true, hgetn, Option.map_some]

/-- Deleting a data identity preserves the circle with exactly that identity erased. -/
public theorem sentinelDelete_circular {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ((store.get x).get hx).prev.isSome)
    (hn : ((store.get x).get hx).next.isSome)
    (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (s : Fin capacity) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) (member : x ∈ ids) :
    CircularRepresents (sentinelDelete store x hx hp hn hprev hnext).ret
      s (ids.erase x) := by
  obtain ⟨before, after, hids⟩ := List.mem_iff_append.mp member
  have ndParts := List.nodup_append.mp (hids ▸ rep.1)
  have hxBefore : x ∉ before := by
    intro hm
    exact ndParts.2.2 x hm x (by simp) rfl
  have hxAfter : x ∉ after := (List.nodup_cons.mp ndParts.2.1).1
  have hxs : x ≠ s := fun he => rep.2.1 (he ▸ member)
  have leftNo : x ∉ s :: before := by simpa [hxs] using hxBefore
  have rightNo : x ∉ after ++ [s] := by simp [hxAfter, hxs]
  have chain := ((circular_chain store s ids).mp rep).2.2
  have selected := selected_edges store s x before after (by simpa [hids] using chain)
  have transport := edge_transport store x (before.getLastD s) (after.headD s)
    hx hp hn hprev hnext selected.1 selected.2
  have old : List.IsChain (circleEdge store) ((s :: before) ++ x :: (after ++ [s])) := by
    simpa only [hids, List.cons_append, List.append_assoc] using chain
  have new := chain_splice old leftNo rightNo transport.1 transport.2
  have eraseEq : ids.erase x = before ++ after := by
    rw [hids, List.erase_append_right (x :: after) hxBefore, List.erase_cons_head]
  apply (circular_chain _ s (ids.erase x)).mpr
  refine ⟨rep.1.erase x, fun hm => rep.2.1 (List.erase_subset hm), ?_⟩
  simpa only [eraseEq, List.cons_append, List.append_assoc] using new

/-- Deletion preserves any disjoint represented circle, including its sentinel. -/
public theorem sentinelDelete_disjoint_circular {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ((store.get x).get hx).prev.isSome)
    (hn : ((store.get x).get hx).next.isSome)
    (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (s t : Fin capacity) (ids otherIds : List (Fin capacity))
    (rep : CircularRepresents store s ids) (member : x ∈ ids)
    (otherRep : CircularRepresents store t otherIds)
    (disjoint : (s :: ids).Disjoint (t :: otherIds)) :
    CircularRepresents (sentinelDelete store x hx hp hn hprev hnext).ret
      t otherIds := by
  obtain ⟨before, after, hids⟩ := List.mem_iff_append.mp member
  obtain ⟨node, hnode, hpv, hnv⟩ := rep.2.2.2 before x after hids
  have hNode : (store.get x).get hx = node :=
    Option.some.inj ((Option.some_get hx).trans hnode)
  apply sentinelDelete_disjoint_neighbors store x hx hp hn hprev hnext t otherIds
    otherRep
  · intro p he
    have hpEq : p = before.getLastD s :=
      Option.some.inj (he.symm.trans (by simpa only [hNode] using hpv))
    subst p
    apply List.disjoint_left.mp disjoint
    rw [hids]
    have hm := List.getLastD_mem_cons (l := before) (a := s)
    rcases List.mem_cons.mp hm with hs | hb
    · exact List.mem_cons.mpr (Or.inl hs)
    · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hb)))
  · intro n he
    have hnEq : n = after.headD s :=
      Option.some.inj (he.symm.trans (by simpa only [hNode] using hnv))
    subst n
    apply List.disjoint_left.mp disjoint
    rw [hids]
    have hm := headD_mem_cons s after
    rcases List.mem_cons.mp hm with hs | ha
    · exact List.mem_cons.mpr (Or.inl hs)
    · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
        (Or.inr (List.mem_cons.mpr (Or.inr ha)))))

end Cslib.Algorithms.Lean.DoublyLinkedList
