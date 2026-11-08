/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat

@[expose] public meta section

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.IndexedMinQueue

private def assertEq {A : Type} [BEq A] [LawfulBEq A] [Repr A]
    (label : String) (actual expected : A) : IO Unit :=
  unless actual == expected do
    throw <| IO.userError s!"{label}: expected {repr expected}, got {repr actual}"

private def needSome {A : Type} (label : String) (x : Option A) : IO A :=
  match x with
  | some a => pure a
  | none => throw <| IO.userError s!"{label}: expected some"

private def costTuple (cost : Fin 5 → Nat) : Nat × Nat × Nat × Nat × Nat :=
  (cost 0, cost 1, cost 2, cost 3, cost 4)

private def heapView {W : Type} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) : Array (WithTop W × Nat) :=
  q.heap.data.map fun entry => ((ofLex entry).1, (ofLex entry).2.val)

private def positionView {W : Type} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) : Array (Option Nat) :=
  q.position.toArray.map (Option.map Fin.val)

private def checkState {W : Type} [LinearOrder W] [BEq W] [LawfulBEq W] [Repr W]
    {n : Nat} (label : String) (q : IndexedMinQueue W n)
    (heap : Array (WithTop W × Nat)) (position : Array (Option Nat)) : IO Unit := do
  assertEq s!"{label} heap" (heapView q) heap
  assertEq s!"{label} position" (positionView q) position

private def checkCost {A : Type} (label : String) (r : TimeM (Fin 5 → Nat) A)
    (expected : Nat × Nat × Nat × Nat × Nat) : IO Unit :=
  assertEq s!"{label} events" (costTuple r.time) expected

private def insertChecked {W : Type} [LinearOrder W] [BEq W] [LawfulBEq W] [Repr W]
    {n : Nat} (label : String) (q : IndexedMinQueue W n) (v : Fin n)
    (key : WithTop W) (heap : Array (WithTop W × Nat))
    (position : Array (Option Nat))
    (cost : Nat × Nat × Nat × Nat × Nat) : IO (IndexedMinQueue W n) := do
  let r := insert q v key
  checkCost label r cost
  let q' ← needSome label r.ret
  checkState label q' heap position
  pure q'

private def decreaseChecked {W : Type} [LinearOrder W] [BEq W] [LawfulBEq W] [Repr W]
    {n : Nat} (label : String) (q : IndexedMinQueue W n) (v : Fin n)
    (key : W) (heap : Array (WithTop W × Nat))
    (position : Array (Option Nat))
    (cost : Nat × Nat × Nat × Nat × Nat) : IO (IndexedMinQueue W n) := do
  let r := decreaseKey q v key
  checkCost label r cost
  let q' ← needSome label r.ret
  checkState label q' heap position
  pure q'

private def extractChecked {W : Type} [LinearOrder W] [BEq W] [LawfulBEq W] [Repr W]
    {n : Nat} (label : String) (q : IndexedMinQueue W n)
    (identity : Nat) (key : WithTop W) (heap : Array (WithTop W × Nat))
    (position : Array (Option Nat))
    (cost : Nat × Nat × Nat × Nat × Nat) : IO (IndexedMinQueue W n) := do
  let r := extractMin q
  checkCost label r cost
  let pair ← needSome label r.ret
  assertEq s!"{label} identity" (ofLex pair.1).2.val identity
  assertEq s!"{label} key" (ofLex pair.1).1 key
  checkState label pair.2 heap position
  pure pair.2

private def zeroCapacityFixture : IO Unit := do
  let q : IndexedMinQueue Int 0 := empty 0
  checkState "zero capacity empty" q #[] #[]
  let result := extractMin q
  checkCost "zero capacity extract" result (0, 0, 0, 0, 0)
  assertEq "zero capacity extract result" result.ret.isNone true
  IO.println "ACTUAL_H_ZERO_CAPACITY heap=[] position=[] extract=none events=(0,0,0,0,0)"

private def primFixture : IO Unit := do
  let q0 : IndexedMinQueue Int 4 := empty 4
  checkState "prim empty" q0 #[] #[none, none, none, none]
  let m0 := member q0 0
  checkCost "prim empty member" m0 (0, 0, 1, 0, 0)
  assertEq "prim empty member result" m0.ret false
  let x0 := extractMin q0
  checkCost "prim empty extract" x0 (0, 0, 0, 0, 0)
  assertEq "prim empty extract result" x0.ret.isNone true
  let d0 := decreaseKey q0 0 (-1)
  checkCost "prim absent decrease" d0 (0, 0, 1, 0, 0)
  assertEq "prim absent decrease result" d0.ret.isNone true

  let q1 ← insertChecked "prim insert 0" q0 0 ⊤
    #[(⊤, 0)] #[some 0, none, none, none] (0, 0, 1, 1, 1)
  let q2 ← insertChecked "prim insert 1" q1 1 ⊤
    #[(⊤, 0), (⊤, 1)] #[some 0, some 1, none, none] (1, 0, 1, 1, 1)
  let q3 ← insertChecked "prim insert root 2" q2 2 (0 : Int)
    #[((0 : Int), 2), (⊤, 1), (⊤, 0)] #[some 2, some 1, some 0, none]
    (1, 1, 1, 3, 1)
  let q4 ← insertChecked "prim insert 3" q3 3 ⊤
    #[((0 : Int), 2), (⊤, 1), (⊤, 0), (⊤, 3)]
    #[some 2, some 1, some 0, some 3] (1, 0, 1, 1, 1)

  let present := member q4 3
  checkCost "prim present member" present (0, 0, 1, 0, 0)
  assertEq "prim present member result" present.ret true

  let duplicate := insert q4 2 (4 : Int)
  checkCost "duplicate insert" duplicate (0, 0, 1, 0, 0)
  assertEq "duplicate insert result" duplicate.ret.isNone true
  checkState "duplicate insert unchanged" q4
    #[((0 : Int), 2), (⊤, 1), (⊤, 0), (⊤, 3)]
    #[some 2, some 1, some 0, some 3]

  let q5 ← extractChecked "prim extract 2" q4 2 (0 : Int)
    #[(⊤, 0), (⊤, 1), (⊤, 3)] #[some 0, some 1, none, some 2]
    (2, 2, 0, 5, 1)
  let q6 ← decreaseChecked "prim decrease 3" q5 3 (-1)
    #[((-1 : Int), 3), (⊤, 1), (⊤, 0)] #[some 2, some 1, none, some 0]
    (2, 1, 1, 2, 1)
  let q7 ← extractChecked "prim extract 3" q6 3 (-1 : Int)
    #[(⊤, 0), (⊤, 1)] #[some 0, some 1, none, none] (1, 1, 0, 3, 1)
  let q8 ← extractChecked "prim extract 0" q7 0 ⊤
    #[(⊤, 1)] #[none, some 0, none, none] (0, 1, 0, 3, 1)
  let q9 ← extractChecked "prim extract 1" q8 1 ⊤
    #[] #[none, none, none, none] (0, 0, 0, 1, 1)
  checkState "prim finished" q9 #[] #[none, none, none, none]
  IO.println "ACTUAL_H_PRIM all returned keys, states, inverse entries and five-event tuples checked"

private def unequalFixture : IO Unit := do
  let q0 : IndexedMinQueue Int 4 := empty 4
  let q1 ← insertChecked "unequal insert 0" q0 0 (7 : Int)
    #[((7 : Int), 0)] #[some 0, none, none, none] (0, 0, 1, 1, 1)
  let q2 ← insertChecked "unequal insert 1" q1 1 (3 : Int)
    #[((3 : Int), 1), ((7 : Int), 0)] #[some 1, some 0, none, none] (1, 1, 1, 3, 1)
  let q3 ← insertChecked "unequal insert 2" q2 2 (9 : Int)
    #[((3 : Int), 1), ((7 : Int), 0), ((9 : Int), 2)]
    #[some 1, some 0, some 2, none] (1, 0, 1, 1, 1)
  let q4 ← insertChecked "unequal insert 3" q3 3 (5 : Int)
    #[((3 : Int), 1), ((5 : Int), 3), ((9 : Int), 2), ((7 : Int), 0)]
    #[some 3, some 0, some 2, some 1] (2, 1, 1, 3, 1)
  let q5 ← decreaseChecked "unequal decrease 2" q4 2 1
    #[((1 : Int), 2), ((5 : Int), 3), ((3 : Int), 1), ((7 : Int), 0)]
    #[some 3, some 2, some 0, some 1] (2, 1, 1, 2, 1)
  let q6 ← extractChecked "unequal extract 2" q5 2 (1 : Int)
    #[((3 : Int), 1), ((5 : Int), 3), ((7 : Int), 0)]
    #[some 2, some 0, none, some 1] (2, 2, 0, 5, 1)
  let q7 ← extractChecked "unequal extract 1" q6 1 (3 : Int)
    #[((5 : Int), 3), ((7 : Int), 0)] #[some 1, none, none, some 0]
    (1, 2, 0, 5, 1)
  let q8 ← extractChecked "unequal extract 3" q7 3 (5 : Int)
    #[((7 : Int), 0)] #[some 0, none, none, none] (0, 1, 0, 3, 1)
  let _q9 ← extractChecked "unequal extract 0" q8 0 (7 : Int)
    #[] #[none, none, none, none] (0, 0, 0, 1, 1)
  IO.println "ACTUAL_H_UNEQUAL all returned keys, states, inverse entries and five-event tuples checked"

private def rationalFixture : IO Unit := do
  let half : Rat := 1 / 2
  let minusHalf : Rat := -1 / 2
  let q0 : IndexedMinQueue Rat 4 := empty 4
  let q1 ← insertChecked "rat equal insert 0" q0 0 half
    #[(half, 0)] #[some 0, none, none, none] (0, 0, 1, 1, 1)
  let q2 ← insertChecked "rat equal insert 1" q1 1 half
    #[(half, 0), (half, 1)] #[some 0, some 1, none, none] (1, 0, 1, 1, 1)
  let q3 ← insertChecked "rat negative insert 2" q2 2 minusHalf
    #[(minusHalf, 2), (half, 1), (half, 0)] #[some 2, some 1, some 0, none]
    (1, 1, 1, 3, 1)
  let q4 ← insertChecked "rat infinite insert 3" q3 3 ⊤
    #[(minusHalf, 2), (half, 1), (half, 0), (⊤, 3)]
    #[some 2, some 1, some 0, some 3] (1, 0, 1, 1, 1)
  let q5 ← decreaseChecked "rat deep decrease" q4 3 (-1)
    #[((-1 : Rat), 3), (minusHalf, 2), (half, 0), (half, 1)]
    #[some 2, some 3, some 1, some 0] (3, 2, 1, 4, 1)
  let q6 ← decreaseChecked "rat repeated decrease" q5 3 (-2)
    #[((-2 : Rat), 3), (minusHalf, 2), (half, 0), (half, 1)]
    #[some 2, some 3, some 1, some 0] (1, 0, 1, 0, 1)

  let equalReject := decreaseKey q6 3 (-2)
  checkCost "rat equal decrease rejection" equalReject (1, 0, 1, 0, 0)
  assertEq "rat equal decrease result" equalReject.ret.isNone true
  checkState "rat equal decrease unchanged" q6
    #[((-2 : Rat), 3), (minusHalf, 2), (half, 0), (half, 1)]
    #[some 2, some 3, some 1, some 0]
  let increaseReject := decreaseKey q6 3 0
  checkCost "rat increasing decrease rejection" increaseReject (1, 0, 1, 0, 0)
  assertEq "rat increasing decrease result" increaseReject.ret.isNone true
  checkState "rat increasing decrease unchanged" q6
    #[((-2 : Rat), 3), (minusHalf, 2), (half, 0), (half, 1)]
    #[some 2, some 3, some 1, some 0]

  let q7 ← extractChecked "rat root replacement" q6 3 (-2 : Rat)
    #[(minusHalf, 2), (half, 1), (half, 0)] #[some 2, some 1, some 0, none]
    (2, 2, 0, 5, 1)
  let q8 ← extractChecked "rat extract negative" q7 2 minusHalf
    #[(half, 0), (half, 1)] #[some 0, some 1, none, none] (1, 1, 0, 3, 1)
  let q9 ← extractChecked "rat deterministic tie 0" q8 0 half
    #[(half, 1)] #[none, some 0, none, none] (0, 1, 0, 3, 1)
  let _q10 ← extractChecked "rat deterministic tie 1" q9 1 half
    #[] #[none, none, none, none] (0, 0, 0, 1, 1)
  IO.println "ACTUAL_H_RATIONAL all returned keys, states, inverse entries and five-event tuples checked"

#eval zeroCapacityFixture
#eval primFixture
#eval unequalFixture
#eval rationalFixture
