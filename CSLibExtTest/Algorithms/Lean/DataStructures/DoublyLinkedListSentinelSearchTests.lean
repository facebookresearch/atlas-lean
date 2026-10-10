/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Sentinel.Search
public meta import Cslib.Algorithms.Lean.TimeM

/-!
# Executed sentinel-search fixtures

The ordinary module hook executes actual public sentinel search. Complete returned
pools, identity and selected-event time are asserted, not predicted by a mock scan.
-/

@[expose] public meta section

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.DoublyLinkedList

private def check {α : Type} [BEq α] [Repr α]
    (label : String) (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: expected {repr expected}, got {repr actual}"
  IO.println s!"{label}: {repr actual}"

private def emptyStore (key : Int) (satellite : String) :
    Vector (Option (Node (Int × String) (Fin 1))) 1 :=
  #v[some ⟨(key, satellite), some 0, some 0⟩]

private lemma emptyValid (key : Int) (satellite : String) :
    ∃ ids, CircularRepresents (emptyStore key satellite) (0 : Fin 1) ids := by
  refine ⟨[], (CircularRepresents_nil _ _).mpr ?_⟩
  exact ⟨⟨(key, satellite), some 0, some 0⟩, rfl, rfl, rfl⟩

private def caseEmpty : IO Unit := do
  let result := listSearchSentinel (emptyStore (-37) "sentinel satellite") 0 (-7)
    (emptyValid (-37) "sentinel satellite")
  check "empty overwritten sentinel full store" result.ret.1
    (emptyStore (-7) "sentinel satellite")
  check "empty overwritten sentinel identity" result.ret.2 none
  check "empty overwritten sentinel selected events" result.time 4

-- Test-only certificate adapted from the landed SentinelDeleteAPITests pairRep.
private lemma pairRep {α : Type*} {capacity : Nat}
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
private def pool (a b : Int) : Vector (Option (Node (Int × String) (Fin 8))) 8 := #v[
  some ⟨(37, "first sentinel"), some 1, some 2⟩,
  some ⟨(a, "first data"), some 2, some 0⟩,
  some ⟨(b, "second data"), some 0, some 1⟩,
  some ⟨(91, "second sentinel"), some 4, some 5⟩,
  some ⟨(7, "other circle head"), some 5, some 3⟩,
  some ⟨(99, "other circle tail"), some 3, some 4⟩,
  none, some ⟨(12345, "detached NIL links"), none, none⟩]

private lemma poolValid (a b : Int) : ∃ ids, CircularRepresents (pool a b) 0 ids := by
  refine ⟨[1, 2], ?_⟩
  apply pairRep (pool a b) 0 1 2
    ⟨(37, "first sentinel"), some 1, some 2⟩
    ⟨(a, "first data"), some 2, some 0⟩
    ⟨(b, "second data"), some 0, some 1⟩ <;> first | rfl | decide

private lemma otherValid (a b : Int) : ∃ ids, CircularRepresents (pool a b) 3 ids := by
  refine ⟨[4, 5], ?_⟩
  apply pairRep (pool a b) 3 4 5
    ⟨(91, "second sentinel"), some 4, some 5⟩
    ⟨(7, "other circle head"), some 5, some 3⟩
    ⟨(99, "other circle tail"), some 3, some 4⟩ <;> first | rfl | decide

private def casePool (label : String) (a b key : Int)
    (expectedId : Option (Fin 8)) (expectedTime : Nat) : IO Unit := do
  let result := listSearchSentinel (pool a b) 0 key (poolValid a b)
  let expected := (pool a b).set 0 (some ⟨(key, "first sentinel"), some 1, some 2⟩)
  check (label ++ " full store") result.ret.1 expected
  check (label ++ " identity") result.ret.2 expectedId
  check (label ++ " selected events") result.time expectedTime

private def caseOther (label : String) (key : Int)
    (expectedId : Option (Fin 8)) (expectedTime : Nat) : IO Unit := do
  let result := listSearchSentinel (pool 3 7) 3 key (otherValid 3 7)
  let expected := (pool 3 7).set 3 (some ⟨(key, "second sentinel"), some 4, some 5⟩)
  check (label ++ " full store") result.ret.1 expected
  check (label ++ " identity") result.ret.2 expectedId
  check (label ++ " selected events") result.time expectedTime

private def singleton : Vector (Option (Node (Int × String) (Fin 2))) 2 :=
  #v[some ⟨(37, "singleton sentinel"), some 1, some 1⟩,
    some ⟨(-9, "negative singleton"), some 0, some 0⟩]

private lemma singletonValid : ∃ ids, CircularRepresents singleton 0 ids := by
  refine ⟨[1], by decide, by decide, ⟨_, rfl, rfl, rfl⟩, ?_⟩
  intro before a after he
  cases before with
  | nil =>
    simp only [List.nil_append] at he
    obtain ⟨ha, ht⟩ := List.cons.inj he
    subst a
    subst after
    exact ⟨_, rfl, rfl, rfl⟩
  | cons b tail =>
    have len := congrArg List.length he
    simp only [List.length_append, List.length_cons, List.length_nil] at len
    omega

private def caseSingleton (label : String) (key : Int)
    (expectedId : Option (Fin 2)) (expectedTime : Nat) : IO Unit := do
  let result := listSearchSentinel singleton 0 key singletonValid
  let expected := singleton.set 0 (some ⟨(key, "singleton sentinel"), some 1, some 1⟩)
  check (label ++ " full store") result.ret.1 expected
  check (label ++ " identity") result.ret.2 expectedId
  check (label ++ " selected events") result.time expectedTime

private def caseEmptySame : IO Unit := do
  let result := listSearchSentinel (emptyStore (-37) "sentinel satellite") 0 (-37)
    (emptyValid (-37) "sentinel satellite")
  check "empty already matching full store" result.ret.1 (emptyStore (-37) "sentinel satellite")
  check "empty already matching identity" result.ret.2 none
  check "empty already matching selected events" result.time 4

private def runCases : IO Unit := do
  caseEmpty
  caseEmptySame
  casePool "first hit" 3 7 3 (some 1) 4
  casePool "tail hit" 3 7 7 (some 2) 6
  casePool "duplicate keys first occurrence" 7 7 7 (some 1) 4
  casePool "absent full circle" 3 7 42 none 8
  casePool "old sentinel key is not a data match" 3 7 37 none 8
  casePool "other circle data excluded" 3 7 99 none 8
  casePool "detached NIL-linked match excluded" 3 7 12345 none 8
  caseOther "second circle head" 7 (some 4) 4
  caseOther "second circle tail" 99 (some 5) 6
  caseSingleton "negative singleton hit" (-9) (some 1) 4
  caseSingleton "singleton miss" 42 none 6

#eval runCases

end
