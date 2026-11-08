/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Insert
public meta import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Insert
public meta import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Basic
public meta import Cslib.Algorithms.Lean.TimeM

/-! Twelve ordinary-build LIST-INSERT executions, including full represented stores and aliases. -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DoublyLinkedList.InsertTests

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.DoublyLinkedList

namespace Represented

private def node (payload : Int × String) (next prev : Option (Fin 7)) :
    Option (Node (Int × String) (Fin 7)) := some { payload, next, prev }

private def initial : Vector (Option (Node (Int × String) (Fin 7))) 7 := ⟨#[
  node (10, "alpha") (some 1) none,
  node (10, "beta") none (some 0),
  node (-5, "inserted") (some 3) (some 5),
  node (10, "other-head") (some 4) none,
  node (-2, "other-middle") (some 5) (some 3),
  node (99, "other-tail") none (some 4),
  none], rfl⟩

private def interior : Vector (Option (Node (Int × String) (Fin 7))) 7 := ⟨#[
  node (10, "alpha") (some 2) none,
  node (10, "beta") none (some 2),
  node (-5, "inserted") (some 1) (some 0),
  node (10, "other-head") (some 4) none,
  node (-2, "other-middle") (some 5) (some 3),
  node (99, "other-tail") none (some 4),
  none], rfl⟩

private theorem first_access :
    ∀ z, ((initial.get 0).get (by decide)).next = some z → (initial.get z).isSome := by
  intro z he
  have hz : (1 : Fin 7) = z := Option.some.inj he
  subst z
  decide


private theorem initial_rep : Represents initial (some 0) [0, 1] := by
  refine ⟨by decide, rfl, ?_⟩
  intro i hi
  have h : i = 0 ∨ i = 1 := by
    simp only [List.length_cons, List.length_nil] at hi
    omega
  rcases h with h | h <;> subst i
  · exact ⟨{ payload := (10, "alpha"), next := some 1, prev := none }, rfl, rfl, rfl⟩
  · exact ⟨{ payload := (10, "beta"), next := none, prev := some 0 }, rfl, rfl, rfl⟩

private theorem other_rep : Represents initial (some 3) [3, 4, 5] := by
  refine ⟨by decide, rfl, ?_⟩
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by
    simp only [List.length_cons, List.length_nil] at hi
    omega
  rcases h with h | h | h <;> subst i
  · exact ⟨{ payload := (10, "other-head"), next := some 4, prev := none }, rfl, rfl, rfl⟩
  · exact ⟨{ payload := (-2, "other-middle"), next := some 5, prev := some 3 }, rfl, rfl, rfl⟩
  · exact ⟨{ payload := (99, "other-tail"), next := none, prev := some 4 }, rfl, rfl, rfl⟩

example : Represents (listInsert initial 2 0 (by decide) (by decide) first_access).ret
    (some 0) [0, 2, 1] := by
  simpa using listInsert_represents initial 2 (some 0) [0, 1] initial_rep
    (by decide) 0 (by decide) (by decide) (by decide) first_access

example : Represents (listInsert initial 2 0 (by decide) (by decide) first_access).ret
    (some 3) [3, 4, 5] := by
  simpa using listInsert_disjoint_represents initial 2 (some 0) (some 3)
    [0, 1] [3, 4, 5] initial_rep other_rep (by
      intro z hz hz'
      simp at hz
      rcases hz with rfl | rfl <;> simp at hz') (by decide)
    0 (by decide) (by decide) (by decide) first_access

private def verifyRep (label : String)
    (store : Vector (Option (Node (Int × String) (Fin 7))) 7)
    (head : Option (Fin 7)) (ids : List (Fin 7)) : IO Unit := do
  unless decide ids.Nodup do
    throw <| IO.userError s!"{label}: repeated identities"
  unless head == ids.head? do
    throw <| IO.userError s!"{label}: wrong head"
  for i in List.range ids.length do
    let some id := ids[i]? | throw <| IO.userError s!"{label}: missing identity {i}"
    let some value := store.get id | throw <| IO.userError s!"{label}: absent represented cell {id}"
    let expectedPrev := if i == 0 then none else ids[i - 1]?
    unless value.prev == expectedPrev do
      throw <| IO.userError s!"{label}: wrong predecessor at {id}"
    unless value.next == ids[i + 1]? do
      throw <| IO.userError s!"{label}: wrong successor at {id}"
  IO.println s!"{label}: represented ids={repr ids}"

private def verifyInsertion (label : String)
    (source : Vector (Option (Node (Int × String) (Fin 7))) 7) (x y : Fin 7)
    (hx : (source.get x).isSome) (hy : (source.get y).isSome)
    (hs : ∀ z, ((source.get y).get hy).next = some z → (source.get z).isSome)
    (expected : Vector (Option (Node (Int × String) (Fin 7))) 7) (expectedTime : Nat)
    (head : Option (Fin 7)) (beforeIds afterIds : List (Fin 7))
    (otherHead : Option (Fin 7)) (otherIds : List (Fin 7)) : IO Unit := do
  verifyRep s!"{label}/before" source head beforeIds
  verifyRep s!"{label}/other before" source otherHead otherIds
  let result := listInsert source x y hx hy hs
  unless result.ret == expected do
    throw <| IO.userError s!"{label}: wrong full store {repr result.ret}"
  unless result.time == expectedTime do
    throw <| IO.userError s!"{label}: got time {result.time}, expected {expectedTime}"
  verifyRep s!"{label}/after" result.ret head afterIds
  verifyRep s!"{label}/other after" result.ret otherHead otherIds
  unless result.ret.get 6 == none do
    throw <| IO.userError s!"{label}: absent cell was allocated"
  for i in List.finRange 7 do
    unless (result.ret.get i).map Node.payload == (source.get i).map Node.payload do
      throw <| IO.userError s!"{label}: payload changed at {i}"
  IO.println s!"{label}: store={repr result.ret}; time={result.time}; absent=6; payloads=7"

private def tailExpected : Vector (Option (Node (Int × String) (Fin 7))) 7 :=
  (initial.set 1 (node (10, "beta") (some 2) (some 0))).set 2
    (node (-5, "inserted") none (some 1))

private theorem tail_access :
    ∀ z, ((initial.get 1).get (by decide)).next = some z → (initial.get z).isSome := by
  intro z he
  cases he

private def singletonSource : Vector (Option (Node (Int × String) (Fin 7))) 7 :=
  initial.set 0 (node (10, "alpha") none none)

private def singletonExpected : Vector (Option (Node (Int × String) (Fin 7))) 7 :=
  (singletonSource.set 0 (node (10, "alpha") (some 2) none)).set 2
    (node (-5, "inserted") none (some 0))

private theorem singleton_access :
    ∀ z, ((singletonSource.get 0).get (by decide)).next = some z →
      (singletonSource.get z).isSome := by
  intro z he
  cases he

private def otherExpected : Vector (Option (Node (Int × String) (Fin 7))) 7 :=
  ((initial.set 2 (node (-5, "inserted") (some 5) (some 4))).set 4
    (node (-2, "other-middle") (some 2) (some 3))).set 5
    (node (99, "other-tail") none (some 2))

private theorem other_access :
    ∀ z, ((initial.get 4).get (by decide)).next = some z → (initial.get z).isSome := by
  intro z he
  have hz : (5 : Fin 7) = z := Option.some.inj he
  subst z
  decide

private def runCases : IO Unit := do
  verifyInsertion "represented interior" initial 2 0 (by decide) (by decide)
    first_access interior 5 (some 0) [0, 1] [0, 2, 1] (some 3) [3, 4, 5]
  verifyInsertion "represented tail" initial 2 1 (by decide) (by decide)
    tail_access tailExpected 4 (some 0) [0, 1] [0, 1, 2] (some 3) [3, 4, 5]
  verifyInsertion "represented singleton" singletonSource 2 0 (by decide) (by decide)
    singleton_access singletonExpected 4 (some 0) [0] [0, 2] (some 3) [3, 4, 5]
  verifyInsertion "represented longer interior" initial 2 4 (by decide) (by decide)
    other_access otherExpected 5 (some 3) [3, 4, 5] [3, 4, 2, 5] (some 0) [0, 1]


end Represented

namespace Aliases

private def node (payload : Int) (next prev : Option (Fin 4)) : Node Int (Fin 4) :=
  { payload, next, prev }

private def allocated {n : Nat} (nodes : Vector (Node Int (Fin n)) n) :
    Vector (Option (Node Int (Fin n))) n := nodes.map some

private theorem allocated_some {n : Nat} (nodes : Vector (Node Int (Fin n)) n)
    (i : Fin n) : ((allocated nodes).get i).isSome := by
  change ((nodes.map some)[i.val]).isSome = true
  simp

private def verify {n : Nat} (label : String)
    (nodes : Vector (Node Int (Fin n)) n) (x y : Fin n)
    (expected : Vector (Option (Node Int (Fin n))) n) (expectedTime : Nat) : IO Unit := do
  let initial := allocated nodes
  let result := listInsert initial x y (allocated_some nodes x)
    (allocated_some nodes y) (by intro z _; exact allocated_some nodes z)
  unless result.ret == expected do
    throw <| IO.userError s!"{label}: wrong whole store; got {repr result.ret}"
  unless result.time == expectedTime do
    throw <| IO.userError s!"{label}: got time {result.time}, expected {expectedTime}"
  IO.println s!"{label}: store={repr result.ret}; time={result.time}"

private def initial : Vector (Node Int (Fin 4)) 4 := ⟨#[
  node 10 (some 1) none,
  node 10 none (some 0),
  node (-5) (some 3) (some 3),
  node 99 none none], rfl⟩

private def interior : Vector (Option (Node Int (Fin 4))) 4 := allocated ⟨#[
  node 10 (some 2) none,
  node 10 none (some 2),
  node (-5) (some 1) (some 0),
  node 99 none none], rfl⟩

private def tail : Vector (Option (Node Int (Fin 4))) 4 := allocated ⟨#[
  node 10 (some 1) none,
  node 10 (some 2) (some 0),
  node (-5) none (some 1),
  node 99 none none], rfl⟩

private def aliasXY : Vector (Option (Node Int (Fin 4))) 4 := allocated ⟨#[
  node 10 (some 0) (some 0),
  node 10 none (some 0),
  node (-5) (some 3) (some 3),
  node 99 none none], rfl⟩

private def aliasSuccessor : Vector (Option (Node Int (Fin 4))) 4 := allocated ⟨#[
  node 10 (some 1) none,
  node 10 (some 1) (some 1),
  node (-5) (some 3) (some 3),
  node 99 none none], rfl⟩

private def selfLoop : Vector (Node Int (Fin 4)) 4 := ⟨#[
  node 10 (some 0) none,
  node 10 none (some 0),
  node (-5) (some 3) (some 3),
  node 99 none none], rfl⟩

private def selfLoopResult : Vector (Option (Node Int (Fin 4))) 4 := allocated ⟨#[
  node 10 (some 2) (some 2),
  node 10 none (some 0),
  node (-5) (some 0) (some 0),
  node 99 none none], rfl⟩

private def tailAliasResult : Vector (Option (Node Int (Fin 4))) 4 := allocated ⟨#[
  node 10 (some 1) none,
  node 10 (some 1) (some 1),
  node (-5) (some 3) (some 3),
  node 99 none none], rfl⟩

private def runCases : IO Unit := do
  verify "interior/repeated payload/stale x/disjoint frame" initial 2 0 interior 5
  verify "tail/NIL branch" initial 2 1 tail 4
  verify "x=y/non-NIL" initial 0 0 aliasXY 5
  verify "x=old successor" initial 1 0 aliasSuccessor 5
  verify "y.next=y/carried final backlink" selfLoop 2 0 selfLoopResult 5
  verify "x=y/y.next=y" selfLoop 0 0 aliasXY 5
  verify "x=y/NIL" initial 1 1 tailAliasResult 4
  let singleton : Vector (Node Int (Fin 1)) 1 := ⟨#[{
    payload := -7,
    next := none,
    prev := none }], rfl⟩
  let singletonExpected : Vector (Option (Node Int (Fin 1))) 1 :=
    allocated ⟨#[{ payload := -7, next := some 0, prev := some 0 }], rfl⟩
  verify "capacity1/self insertion" singleton 0 0 singletonExpected 4


end Aliases

private def runCases : IO Unit := do
  Represented.runCases
  Aliases.runCases

#eval runCases

end Cslib.Algorithms.Lean.DoublyLinkedList.InsertTests
