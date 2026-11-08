/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Correctness
public import CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Costs
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Algebra.Group.Nat.Defs

/-! Populated first-discovery, PRINT-PATH and selected-event runtime regressions.

CLRS Figure 20.3 uses codes r=0, s=1, t=2, u=3, v=4, w=5, x=6, y=7, z=8.
Its nine-vertex graph and neighbor order reproduce the printed queue and parent tree.
Every fixture checks the entire distance/parent table and every returned endpoint path.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BreadthFirstSearch

private def finGraph (n : Nat) (adjacency : Fin n → List (Fin n)) :
    DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency := adjacency

private def diamond : DirectedAdjacency (Fin 4) :=
  finGraph 4 (fun vertex => match vertex.val with
    | 0 => [0, 1, 2]
    | 1 => [3]
    | 2 => [3]
    | _ => [])

private def reversedDiamond : DirectedAdjacency (Fin 4) :=
  finGraph 4 (fun vertex => match vertex.val with
    | 0 => [2, 1]
    | 1 => [3]
    | 2 => [3]
    | _ => [])

private def duplicates : DirectedAdjacency (Fin 5) :=
  finGraph 5 (fun vertex => match vertex.val with
    | 0 => [0, 1, 1, 2]
    | 1 => [0, 3, 3]
    | 2 => [3, 2]
    | 3 => [1]
    | _ => [4, 4, 4, 4, 4])

private def fifo : DirectedAdjacency (Fin 6) :=
  finGraph 6 (fun vertex => match vertex.val with
    | 0 => [1, 2]
    | 1 => [3]
    | 2 => [4]
    | 3 => [4]
    | 4 => [5]
    | _ => [])

private def disconnected : DirectedAdjacency (Fin 6) :=
  finGraph 6 (fun vertex => match vertex.val with
    | 0 => [1]
    | 1 => []
    | 2 => [3, 4, 5]
    | 3 => [2]
    | 4 => [4]
    | _ => [2])

private def cycle : DirectedAdjacency (Fin 4) :=
  finGraph 4 (fun vertex => match vertex.val with
    | 0 => [1]
    | 1 => [2]
    | 2 => [3]
    | _ => [0])

private def singleton : DirectedAdjacency (Fin 1) :=
  finGraph 1 (fun vertex => match vertex.val with
    | _ => [])

private def clrs : DirectedAdjacency (Fin 9) :=
  finGraph 9 (fun vertex => match vertex.val with
    | 0 => [1, 2, 5]
    | 1 => [0, 3, 4]
    | 2 => [0, 3]
    | 3 => [1, 2, 7]
    | 4 => [1, 5, 7]
    | 5 => [0, 4, 6, 8]
    | 6 => [5, 7, 8]
    | 7 => [3, 4, 6]
    | _ => [5, 6])

private def verify {V : Type} [BEq V] [Hashable V] [LawfulBEq V]
    (name : String) (graph : DirectedAdjacency V) (source : V) (encode : V → Nat)
    (expectedOrder : List Nat) (expectedTable : List (Nat × Option Nat × Option Nat))
    (expectedTime : Nat) (expectedPaths : List (Nat × Option (List Nat) × Nat)) : IO Unit := do
  let result := bfsWithParents graph source
  let order := result.ret.order.map encode
  let table := graph.vertices.map fun vertex =>
    (encode vertex, result.ret.distance vertex, (result.ret.predecessor vertex).map encode)
  let paths := graph.vertices.map fun vertex =>
    let path := result.ret.pathTo? source vertex
    (encode vertex, path.ret.map (List.map encode), path.time)
  let old := bfs graph source
  if order != expectedOrder || table != expectedTable || result.time != expectedTime ||
      paths != expectedPaths || old.order.map encode != order ||
      graph.vertices.map old.distance != graph.vertices.map result.ret.distance then
    throw <| IO.userError s!"{name}: order={order}, table={table}, events={result.time},
      paths={paths}"
  IO.println s!"{name}: order={order}, table={table}, events={result.time}, paths={paths}"

private def longChain : DirectedAdjacency (Fin 16) :=
  finGraph 16 (fun vertex =>
    if h : vertex.val + 1 < 16 then [⟨vertex.val + 1, h⟩] else [])

private def reversedEnumeration : DirectedAdjacency (Fin 4) where
  vertices := (List.finRange 4).reverse
  vertices_nodup := List.nodup_reverse.mpr (List.nodup_finRange 4)
  vertices_complete vertex := by simp
  adjacency := reversedDiamond.adjacency

private inductive Colliding
  | source | left | right | target
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq

private instance : Hashable Colliding := ⟨fun _ => 0⟩

private def collidingCode : Colliding → Nat
  | .source => 0
  | .left => 1
  | .right => 2
  | .target => 3

private def collidingGraph : DirectedAdjacency Colliding where
  vertices := [.source, .left, .right, .target]
  vertices_nodup := by decide
  vertices_complete vertex := by cases vertex <;> simp
  adjacency
    | .source => [.right, .left]
    | .left => [.target]
    | .right => [.target]
    | .target => []

private def verifyAll : IO Unit := do
  verify "diamond/source-loop" diamond 0 Fin.val [0, 1, 2, 3]
    [(0, some 0, none), (1, some 1, some 0), (2, some 1, some 0), (3, some 2, some 1)]
    16 [(0, some [0], 2), (1, some [0, 1], 5), (2, some [0, 2], 5), (3, some [0, 1, 3], 8)]
  verify "reversed-diamond" reversedDiamond 0 Fin.val [0, 2, 1, 3]
    [(0, some 0, none), (1, some 1, some 0), (2, some 1, some 0), (3, some 2, some 2)]
    15 [(0, some [0], 2), (1, some [0, 1], 5), (2, some [0, 2], 5), (3, some [0, 2, 3], 8)]
  verify "duplicates/cycles/unscanned-component" duplicates 0 Fin.val [0, 1, 2, 3]
    [(0, some 0, none), (1, some 1, some 0), (2, some 1, some 0), (3, some 2, some 1), (4, none,
      none)]
    22 [(0, some [0], 2), (1, some [0, 1], 5), (2, some [0, 2], 5), (3, some [0, 1, 3], 8), (4,
      none, 2)]
  verify "FIFO-not-DFS" fifo 0 Fin.val [0, 1, 2, 3, 4, 5]
    [(0, some 0, none), (1, some 1, some 0), (2, some 1, some 0), (3, some 2, some 1), (4,
      some 2, some 2), (5, some 3, some 4)]
    23 [(0, some [0], 2), (1, some [0, 1], 5), (2, some [0, 2], 5), (3, some [0, 1, 3], 8), (4,
      some [0, 2, 4], 8), (5, some [0, 2, 4, 5], 11)]
  verify "disconnected/stuttering-attempts" disconnected 0 Fin.val [0, 1]
    [(0, some 0, none), (1, some 1, some 0), (2, none, none), (3, none, none), (4, none, none),
      (5, none, none)]
    10 [(0, some [0], 2), (1, some [0, 1], 5), (2, none, 2), (3, none, 2), (4, none, 2), (5,
      none, 2)]
  verify "directed-cycle" cycle 0 Fin.val [0, 1, 2, 3]
    [(0, some 0, none), (1, some 1, some 0), (2, some 2, some 1), (3, some 3, some 2)]
    15 [(0, some [0], 2), (1, some [0, 1], 5), (2, some [0, 1, 2], 8), (3, some [0, 1, 2, 3], 11)]
  verify "zero-edge-singleton" singleton 0 Fin.val [0]
    [(0, some 0, none)]
    2 [(0, some [0], 2)]
  verify "CLRS-Figure-20.3" clrs 1 Fin.val [1, 0, 3, 4, 2, 5, 7, 6, 8]
    [(0, some 1, some 1), (1, some 0, none), (2, some 2, some 0), (3, some 1, some 1), (4,
      some 1, some 1), (5, some 2, some 0), (6, some 3, some 5), (7, some 2, some 3), (8, some 3,
      some 5)]
    52 [(0, some [1, 0], 5), (1, some [1], 2), (2, some [1, 0, 2], 8), (3, some [1, 3], 5), (4,
      some [1, 4], 5), (5, some [1, 0, 5], 8), (6, some [1, 0, 5, 6], 11), (7, some [1, 3, 7],
      8), (8, some [1, 0, 5, 8], 11)]
  verify "long-chain" longChain 0 Fin.val (List.range 16)
    ((List.range 16).map fun vertex =>
      (vertex, some vertex, if vertex = 0 then none else some (vertex - 1)))
    62 ((List.range 16).map fun vertex =>
      (vertex, some (List.range (vertex + 1)), 3 * vertex + 2))
  verify "reversed-enumeration" reversedEnumeration 0 Fin.val [0, 2, 1, 3]
    [(3, some 2, some 2), (2, some 1, some 0), (1, some 1, some 0), (0, some 0, none)]
    15 [(3, some [0, 2, 3], 8), (2, some [0, 2], 5), (1, some [0, 1], 5), (0, some [0], 2)]
  verify "lawful-equality/hash-collisions" collidingGraph .source collidingCode [0, 2, 1, 3]
    [(0, some 0, none), (1, some 1, some 0), (2, some 1, some 0), (3, some 2, some 2)]
    15 [(0, some [0], 2), (1, some [0, 1], 5), (2, some [0, 2], 5), (3, some [0, 2, 3], 8)]
  IO.println "all 11 predecessor/path/event fixtures passed"

#eval verifyAll
