/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Graph.TransitiveClosure

@[expose] public meta section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TransitiveClosure.Tests

open Cslib.Algorithms.Lean.TransitiveClosure

private def matrixArray {n : Nat} (matrix : Fin n → Fin n → Bool) : Array (Array Bool) :=
  Array.ofFn fun i => Array.ofFn fun j => matrix i j

private def stageArray {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (pivots : Nat) (hpivots : pivots ≤ n) : Array (Array Bool) :=
  (transitiveClosureStages adjacency pivots hpivots).ret.toArray.map Vector.toArray

private def closureArray {n : Nat} (adjacency : Fin n → Fin n → Bool) :
    Array (Array Bool) :=
  matrixArray (transitiveClosure adjacency).ret

private def assertEq {α : Type*} [BEq α] [Repr α]
    (label : String) (actual expected : α) : IO Unit :=
  if actual == expected then
    IO.println s!"{label}: {repr actual}"
  else
    throw <| IO.userError s!"{label}: expected {repr expected}, got {repr actual}"

private def assertRejects (label : String) (action : IO Unit) : IO Unit := do
  let rejection ← try
    action
    pure none
  catch error =>
    pure (some error)
  match rejection with
  | none => throw <| IO.userError s!"{label}: expected rejection"
  | some error => IO.println s!"{label}: rejected ({error})"

private def figureAdjacency (i j : Fin 4) : Bool :=
  (i.val == 1 && j.val == 2) ||
  (i.val == 1 && j.val == 3) ||
  (i.val == 2 && j.val == 1) ||
  (i.val == 3 && j.val == 0) ||
  (i.val == 3 && j.val == 2)

private def figureStage0 : Array (Array Bool) :=
  #[#[true, false, false, false],
    #[false, true, true, true],
    #[false, true, true, false],
    #[true, false, true, true]]

private def figureStage1 : Array (Array Bool) :=
  #[#[true, false, false, false],
    #[false, true, true, true],
    #[false, true, true, false],
    #[true, false, true, true]]

private def figureStage2 : Array (Array Bool) :=
  #[#[true, false, false, false],
    #[false, true, true, true],
    #[false, true, true, true],
    #[true, false, true, true]]

private def figureStage3 : Array (Array Bool) :=
  #[#[true, false, false, false],
    #[false, true, true, true],
    #[false, true, true, true],
    #[true, true, true, true]]

private def figureStage4 : Array (Array Bool) :=
  #[#[true, false, false, false],
    #[true, true, true, true],
    #[true, true, true, true],
    #[true, true, true, true]]

#eval do
  assertEq "Figure 23.5 stage 0" (stageArray figureAdjacency 0 (by omega)) figureStage0
  assertEq "Figure 23.5 stage 1" (stageArray figureAdjacency 1 (by omega)) figureStage1
  assertEq "Figure 23.5 stage 2" (stageArray figureAdjacency 2 (by omega)) figureStage2
  assertEq "Figure 23.5 stage 3" (stageArray figureAdjacency 3 (by omega)) figureStage3
  assertEq "Figure 23.5 stage 4" (stageArray figureAdjacency 4 (by omega)) figureStage4
  assertEq "Figure 23.5 closure" (closureArray figureAdjacency) figureStage4
  assertEq "Figure 23.5 initialization assignments"
    (transitiveClosureStages figureAdjacency 0 (by omega)).time 16
  assertEq "Figure 23.5 first stage assignments"
    ((transitiveClosureStages figureAdjacency 1 (by omega)).time -
      (transitiveClosureStages figureAdjacency 0 (by omega)).time) 16
  assertEq "Figure 23.5 second stage assignments"
    ((transitiveClosureStages figureAdjacency 2 (by omega)).time -
      (transitiveClosureStages figureAdjacency 1 (by omega)).time) 16
  assertEq "Figure 23.5 third stage assignments"
    ((transitiveClosureStages figureAdjacency 3 (by omega)).time -
      (transitiveClosureStages figureAdjacency 2 (by omega)).time) 16
  assertEq "Figure 23.5 fourth stage assignments"
    ((transitiveClosureStages figureAdjacency 4 (by omega)).time -
      (transitiveClosureStages figureAdjacency 3 (by omega)).time) 16
  assertEq "Figure 23.5 total assignments" (transitiveClosure figureAdjacency).time 80

private def emptyAdjacency (i _ : Fin 0) : Bool := nomatch i

#eval do
  assertEq "empty closure" (closureArray emptyAdjacency) #[]
  assertEq "empty assignments" (transitiveClosure emptyAdjacency).time 0

private def singletonNoEdge (_ _ : Fin 1) : Bool := false
private def singletonSelfLoop (_ _ : Fin 1) : Bool := true
private def singletonClosure : Array (Array Bool) := #[#[true]]

#eval do
  assertEq "singleton without self-loop" (closureArray singletonNoEdge) singletonClosure
  assertEq "singleton without self-loop assignments" (transitiveClosure singletonNoEdge).time 2
  assertEq "singleton with self-loop" (closureArray singletonSelfLoop) singletonClosure
  assertEq "singleton with self-loop assignments" (transitiveClosure singletonSelfLoop).time 2

private def disconnectedAdjacency (_ _ : Fin 3) : Bool := false
private def disconnectedClosure : Array (Array Bool) :=
  #[#[true, false, false],
    #[false, true, false],
    #[false, false, true]]

#eval do
  assertEq "disconnected closure" (closureArray disconnectedAdjacency) disconnectedClosure
  assertEq "disconnected assignments" (transitiveClosure disconnectedAdjacency).time 36

private def twoWayCycleAdjacency (i j : Fin 3) : Bool :=
  (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0)

private def twoWayCycleClosure : Array (Array Bool) :=
  #[#[true, true, false],
    #[true, true, false],
    #[false, false, true]]

#eval do
  assertEq "two-way cycle closure" (closureArray twoWayCycleAdjacency) twoWayCycleClosure
  assertEq "two-way cycle assignments" (transitiveClosure twoWayCycleAdjacency).time 36

private def nonmonotoneChainAdjacency (i j : Fin 4) : Bool :=
  (i.val == 2 && j.val == 0) ||
  (i.val == 0 && j.val == 3) ||
  (i.val == 3 && j.val == 1)

private def nonmonotoneChainClosure : Array (Array Bool) :=
  #[#[true, true, false, true],
    #[false, true, false, false],
    #[true, true, true, true],
    #[false, true, false, true]]

#eval do
  assertEq "non-monotone multi-pivot chain"
    (closureArray nonmonotoneChainAdjacency) nonmonotoneChainClosure
  assertEq "non-monotone multi-pivot assignments"
    (transitiveClosure nonmonotoneChainAdjacency).time 80

private def isolatedVertexAdjacency (i j : Fin 4) : Bool :=
  (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 2)

private def isolatedVertexClosure : Array (Array Bool) :=
  #[#[true, true, true, false],
    #[false, true, true, false],
    #[false, false, true, false],
    #[false, false, false, true]]

#eval do
  assertEq "isolated vertex closure" (closureArray isolatedVertexAdjacency) isolatedVertexClosure
  assertEq "isolated vertex assignments" (transitiveClosure isolatedVertexAdjacency).time 80

-- These caught failures establish that the executable assertions reject the three relevant
-- classes of bad expectation.
#eval assertRejects "negative control: wrong diagonal" <|
  assertEq "wrong diagonal" (closureArray singletonNoEdge) #[#[false]]

#eval assertRejects "negative control: wrong final entry" <|
  assertEq "wrong final entry" (closureArray figureAdjacency) figureStage3

#eval assertRejects "negative control: wrong assignment count" <|
  assertEq "wrong assignment count" (transitiveClosure figureAdjacency).time 79

example {n : Nat} (adjacency : Fin n → Fin n → Bool) (i j : Fin n) :
    (transitiveClosure adjacency).ret i j = true ↔
      Relation.ReflTransGen (fun a b => adjacency a b = true) i j :=
  transitiveClosure_cell_eq_true_iff adjacency i j

example {n : Nat} (adjacency : Fin n → Fin n → Bool) :
    (transitiveClosure adjacency).time = n ^ 2 + n ^ 3 :=
  transitiveClosure_time adjacency

end Cslib.Algorithms.Lean.TransitiveClosure.Tests
