/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Sentinel.Delete

/-!
# Ordinary circular-sentinel deletion API tests

The frozen facade is used without import-all. Generic erasure/disjointness and
concrete empty, singleton, multi-node, two-circle, absent and detached witnesses
reuse the settled mathematical consumer proofs.
-/

public section

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.DoublyLinkedList

universe u

#check @CircularRepresents
#check @CircularRepresents_nil
#check @sentinelDelete
#check @sentinelDelete_time
#check @sentinelDelete_ret
#check @sentinelDelete_get
#check @sentinelDelete_frame
#check @sentinelDelete_allocated
#check @sentinelDelete_payload
#check @sentinelDelete_deleted_record
#check @sentinelDelete_circular
#check @sentinelDelete_disjoint_circular

private lemma emptyRep {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity)
    (s : Fin capacity) (node : Node α (Fin capacity))
    (hs : store.get s = some node) (hn : node.next = some s) (hp : node.prev = some s) :
    CircularRepresents store s [] := by
  refine ⟨by simp, by simp, ⟨node, hs, hn, hp⟩, ?_⟩
  intro before a after he
  have len := congrArg List.length he
  simp only [List.length_nil, List.length_append, List.length_cons] at len
  omega

private lemma singletonRep {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (s x : Fin capacity)
    (sentinel node : Node α (Fin capacity)) (sx : s ≠ x)
    (hs : store.get s = some sentinel) (hx : store.get x = some node)
    (hsn : sentinel.next = some x) (hsp : sentinel.prev = some x)
    (hn : node.next = some s) (hp : node.prev = some s) :
    CircularRepresents store s [x] := by
  refine ⟨by simp, by simpa using sx, ⟨sentinel, hs, hsn, hsp⟩, ?_⟩
  intro before a after he
  cases before with
  | nil =>
    simp only [List.nil_append] at he
    obtain ⟨ha, ht⟩ := List.cons.inj he
    subst a
    subst after
    exact ⟨node, hx, hp, hn⟩
  | cons b tail =>
    have len := congrArg List.length he
    simp only [List.length_append, List.length_cons, List.length_nil] at len
    omega

private lemma pairRep {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (s x y : Fin capacity)
    (sentinel nx ny : Node α (Fin capacity)) (sx : s ≠ x) (sy : s ≠ y) (xy : x ≠ y)
    (hs : store.get s = some sentinel) (hx : store.get x = some nx)
    (hy : store.get y = some ny) (hsn : sentinel.next = some x) (hsp : sentinel.prev = some y)
    (hxp : nx.prev = some s) (hxn : nx.next = some y)
    (hyp : ny.prev = some x) (hyn : ny.next = some s) :
    CircularRepresents store s [x, y] := by
  refine ⟨by simp [xy], by simp [sx, sy], ⟨sentinel, hs, hsn, hsp⟩, ?_⟩
  intro before a after he
  cases before with
  | nil =>
    simp only [List.nil_append] at he
    obtain ⟨ha, ht⟩ := List.cons.inj he
    subst a
    subst after
    exact ⟨nx, hx, hxp, hxn⟩
  | cons b tail =>
    simp only [List.cons_append] at he
    obtain ⟨hb, ht⟩ := List.cons.inj he
    subst b
    cases tail with
    | nil =>
      simp only [List.nil_append] at ht
      obtain ⟨ha, ht⟩ := List.cons.inj ht
      subst a
      subst after
      exact ⟨ny, hy, hyp, hyn⟩
    | cons c rest =>
      have len := congrArg List.length ht
      simp only [List.length_append, List.length_cons, List.length_nil] at len
      omega

private def emptyNodes : Vector (Node (Int × String) (Fin 1)) 1 := ⟨#[
  { payload := (-3, "empty sentinel"), next := some 0, prev := some 0 }], rfl⟩

example : CircularRepresents (emptyNodes.map some) 0 [] := by
  apply emptyRep _ _ (emptyNodes.get 0) <;> simp [emptyNodes, Vector.get]

private def singletonNodes : Vector (Node (Int × String) (Fin 2)) 2 := ⟨#[
  { payload := (10, "sentinel"), next := some 1, prev := some 1 },
  { payload := (10, "different satellite"), next := some 0, prev := some 0 }], rfl⟩

example : CircularRepresents (singletonNodes.map some) 0 [1] := by
  apply singletonRep _ _ _ (singletonNodes.get 0) (singletonNodes.get 1) <;>
    simp [singletonNodes, Vector.get, Fin.cast]

private def pairNodes : Vector (Node (Int × String) (Fin 3)) 3 := ⟨#[
  { payload := (9, "sentinel"), next := some 1, prev := some 2 },
  { payload := (9, "first satellite"), next := some 2, prev := some 0 },
  { payload := (9, "second satellite"), next := some 0, prev := some 1 }], rfl⟩

example : CircularRepresents (pairNodes.map some) 0 [1, 2] := by
  apply pairRep _ _ _ _ (pairNodes.get 0) (pairNodes.get 1) (pairNodes.get 2) <;>
    simp [pairNodes, Vector.get, Fin.cast]

example {α : Type u} {capacity : Nat}
    (store : Vector (Option (Node α (Fin capacity))) capacity) (x : Fin capacity)
    (hx : (store.get x).isSome)
    (hp : ((store.get x).get hx).prev.isSome)
    (hn : ((store.get x).get hx).next.isSome)
    (hprev : ∀ p, ((store.get x).get hx).prev = some p → (store.get p).isSome)
    (hnext : ∀ n, ((store.get x).get hx).next = some n → (store.get n).isSome)
    (s : Fin capacity) (ids : List (Fin capacity))
    (rep : CircularRepresents store s ids) (member : x ∈ ids) :
    CircularRepresents (sentinelDelete store x hx hp hn hprev hnext).ret
      s (ids.erase x) :=
  sentinelDelete_circular store x hx hp hn hprev hnext s ids rep member

example {α : Type u} {capacity : Nat}
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
      t otherIds :=
  sentinelDelete_disjoint_circular store x hx hp hn hprev hnext s t ids otherIds
    rep member otherRep disjoint

private def circles : Vector (Option (Node (Int × String) (Fin 8))) 8 := #v[
  some ⟨(0, "first sentinel"), some 1, some 2⟩,
  some ⟨(9, "first circle head"), some 2, some 0⟩,
  some ⟨(9, "first circle tail"), some 0, some 1⟩,
  some ⟨(0, "second sentinel"), some 4, some 5⟩,
  some ⟨(9, "second circle head"), some 5, some 3⟩,
  some ⟨(9, "second circle tail"), some 3, some 4⟩,
  none, some ⟨(-3, "detached"), some 7, some 7⟩]

private lemma firstRep : CircularRepresents circles 0 [1, 2] := by
  apply pairRep circles 0 1 2
    ⟨(0, "first sentinel"), some 1, some 2⟩
    ⟨(9, "first circle head"), some 2, some 0⟩
    ⟨(9, "first circle tail"), some 0, some 1⟩ <;> first | rfl | decide

private lemma secondRep : CircularRepresents circles 3 [4, 5] := by
  apply pairRep circles 3 4 5
    ⟨(0, "second sentinel"), some 4, some 5⟩
    ⟨(9, "second circle head"), some 5, some 3⟩
    ⟨(9, "second circle tail"), some 3, some 4⟩ <;> first | rfl | decide

private def result := sentinelDelete circles 1 (by rfl) (by rfl) (by rfl)
  (by intro p he; cases Option.some.inj he; rfl)
  (by intro n he; cases Option.some.inj he; rfl)

example : CircularRepresents result.ret 0 [2] := by
  exact sentinelDelete_circular circles 1 _ _ _ _ _ 0 [1, 2] firstRep (by decide)

example : CircularRepresents result.ret 3 [4, 5] := by
  exact sentinelDelete_disjoint_circular circles 1 _ _ _ _ _ 0 3 [1, 2] [4, 5]
    firstRep (by decide) secondRep (by
      apply List.disjoint_left.mpr
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · decide
      rcases List.mem_cons.mp ha with rfl | ha
      · decide
      rcases List.mem_cons.mp ha with rfl | ha
      · decide
      cases ha)

example : result.ret.get 6 = none := by
  exact (sentinelDelete_frame circles 1 _ _ _ _ _ 6 (by decide) (by decide))

example : result.ret.get 7 = circles.get 7 :=
  sentinelDelete_frame circles 1 _ _ _ _ _ 7 (by decide) (by decide)
