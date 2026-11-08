/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Graph.Prim
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# Prim runtime fixtures

Each assertion runs the public source-order indexed-heap executor and inspects its
returned parents and all seven same-execution event coordinates.
-/

@[expose] public meta section

open Cslib.Algorithms.Lean

namespace PrimTests

def triangle : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency v := if v = 0 then [1, 2] else if v = 1 then [0, 2] else [0, 1]

def signedWeight (e : Sym2 (Fin 3)) : Int :=
  if e = s(0, 1) then -3 else if e = s(1, 2) then 1 else 5

def assertEq {A : Type} [BEq A] [LawfulBEq A] [Repr A]
    (label : String) (actual expected : A) : IO Unit :=
  if actual == expected then pure ()
  else throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def heapTuple (c : Fin 5 → Nat) : Nat × Nat × Nat × Nat × Nat :=
  (c 0, c 1, c 2, c 3, c 4)

def singleton : DirectedAdjacency (Fin 1) where
  vertices := [0]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency _ := []

def disconnected : DirectedAdjacency (Fin 4) where
  vertices := [0, 1, 2, 3]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency v := if v = 0 then [1] else if v = 1 then [0]
    else if v = 2 then [3] else [2]

def disconnectedWeight (e : Sym2 (Fin 4)) : Int :=
  if e = s(0, 1) then -2 else -5

def duplicateTriangle : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency v := if v = 0 then [1, 1, 2] else if v = 1 then [0, 0, 2] else [0, 1]

def reorderedTriangle : DirectedAdjacency (Fin 3) where
  vertices := [2, 1, 0]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency := triangle.adjacency

def isolated : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency _ := []

def zeroPath : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency v := if v = 0 then [1] else if v = 1 then [0, 2] else [1]

def reversedTriangle : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency v := if v = 0 then [2, 1] else if v = 1 then [2, 0] else [1, 0]

def loopedTriangle : DirectedAdjacency (Fin 3) where
  vertices := [0, 1, 2]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency v := v :: triangle.adjacency v

def fractionalWeight (e : Sym2 (Fin 3)) : Rat :=
  if e = s(0, 1) then -3 / 2 else if e = s(1, 2) then 1 / 3 else 5

def verify {W : Type} [LinearOrder W] [Zero W] {n : Nat}
    (label : String) (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (root : Fin n) (parents : List (Option (Fin n))) (inspections tests : Nat)
    (heap : Nat × Nat × Nat × Nat × Nat) : IO Unit := do
  let actual := Prim.prim graph weight root
  assertEq (label ++ " parents") actual.ret.toList parents
  assertEq (label ++ " inspections") actual.time.2.1 inspections
  assertEq (label ++ " key tests") actual.time.2.2 tests
  assertEq (label ++ " heap") (heapTuple actual.time.1) heap
  IO.println <| s!"{label}: parents={repr actual.ret.toList}, heap={heapTuple actual.time.1}, " ++
    s!"inspections={actual.time.2.1}, tests={actual.time.2.2}"

def figureGraph : DirectedAdjacency (Fin 9) where
  vertices := [0, 1, 2, 3, 4, 5, 6, 7, 8]
  vertices_nodup := by decide
  vertices_complete := by decide
  adjacency v := match v.val with
    | 0 => [1, 7]
    | 1 => [0, 2, 7]
    | 2 => [1, 3, 5, 8]
    | 3 => [2, 4, 5]
    | 4 => [3, 5]
    | 5 => [2, 3, 4, 6]
    | 6 => [5, 7, 8]
    | 7 => [0, 1, 6, 8]
    | _ => [2, 6, 7]

def figureEdges : List (Sym2 (Fin 9) × Int) :=
  [(s(0, 1), 4), (s(0, 7), 8), (s(1, 2), 8), (s(1, 7), 11),
    (s(2, 3), 7), (s(2, 5), 4), (s(2, 8), 2), (s(3, 4), 9),
    (s(3, 5), 14), (s(4, 5), 10), (s(5, 6), 2), (s(6, 7), 1),
    (s(6, 8), 6), (s(7, 8), 7)]

def figureWeight (edge : Sym2 (Fin 9)) : Int :=
  ((figureEdges.find? (fun item => item.1 == edge)).map Prod.snd).getD 0

def verifyFigure (args : List String) : IO Unit := do
  assertEq "Figure21.5 vertex order" figureGraph.vertices [0, 1, 2, 3, 4, 5, 6, 7, 8]
  assertEq "Figure21.5 all fourteen edge weights" (figureEdges.map Prod.snd)
    [4, 8, 8, 11, 7, 4, 2, 9, 14, 10, 2, 1, 6, 7]
  assertEq "Figure21.5 undirected edge count" figureEdges.length 14
  assertEq "Figure21.5 adjacency" (figureGraph.vertices.map figureGraph.adjacency)
    [[1, 7], [0, 2, 7], [1, 3, 5, 8], [2, 4, 5], [3, 5], [2, 3, 4, 6],
      [5, 7, 8], [0, 1, 6, 8], [2, 6, 7]]
  for v in figureGraph.vertices do
    for u in figureGraph.adjacency v do
      unless (figureGraph.adjacency u).contains v do
        throw (IO.userError "Figure21.5 adjacency is not symmetric")
      unless figureEdges.any (fun item => item.1 == Sym2.mk u v) do
        throw (IO.userError "Figure21.5 adjacency occurrence is not a source edge")
  let actual := Prim.prim figureGraph figureWeight 0
  assertEq "Figure21.5 all nine parents" actual.ret.toList
    (if args.contains "--wrong-figure-parent" then
      [none, some 0, some 1, some 2, some 3, some 2, some 5, some 0, some 2]
     else [none, some 0, some 1, some 2, some 3, some 2, some 5, some 6, some 2])
  assertEq "Figure21.5 five heap coordinates" (heapTuple actual.time.1)
    (if args.contains "--wrong-figure-heap" then (55, 29, 49, 76, 30)
     else (54, 29, 49, 76, 30))
  assertEq "Figure21.5 inspections" actual.time.2.1
    (if args.contains "--wrong-figure-inspections" then 29 else 28)
  assertEq "Figure21.5 key tests" actual.time.2.2 14
  let selected := (List.finRange 9).filterMap fun v =>
    (actual.ret[v]).map (fun p => Sym2.mk p v)
  assertEq "Figure21.5 selected source edges"
    (selected == [s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(2, 5), s(5, 6), s(6, 7), s(2, 8)]) true
  assertEq "Figure21.5 selected edge count" selected.length 8
  let selectedWeight := (selected.map figureWeight).sum
  assertEq "Figure21.5 selected minimum weight" selectedWeight
    (if args.contains "--wrong-figure-weight" then 36 else 37)
  assertEq "Figure21.5 root is NIL" actual.ret[0] none
  for v in List.finRange 9 do
    let mut current := v
    for _ in List.range 9 do
      match actual.ret[current] with
      | none => pure ()
      | some parent => current := parent
    assertEq "Figure21.5 every parent chain reaches root" current (0 : Fin 9)
  let derivedKeys := (List.finRange 9).map fun v =>
    ((actual.ret[v]).map (fun p => figureWeight (Sym2.mk p v))).getD 0
  assertEq "Figure21.5 derived keys by vertex" derivedKeys [0, 4, 8, 7, 9, 4, 2, 1, 2]
  IO.println <| s!"Figure21.5: parents={repr actual.ret.toList}, " ++
    s!"heap={heapTuple actual.time.1}, inspections={actual.time.2.1}, " ++
    s!"tests={actual.time.2.2}, weight={selectedWeight}, keys={repr derivedKeys}"

def main (args : List String) : IO Unit := do
  let actual := Prim.prim triangle signedWeight 0
  assertEq "signed parents" actual.ret.toList
    (if args.contains "--wrong-parent" then [none, some 2, some 1]
      else [none, some 0, some 1])
  assertEq "signed heap" (heapTuple actual.time.1)
    (if args.contains "--wrong-heap" then (8, 3, 12, 12, 9) else (7, 3, 12, 12, 9))
  assertEq "signed inspections" actual.time.2.1
    (if args.contains "--wrong-inspections" then 7 else 6)
  assertEq "signed key tests" actual.time.2.2
    (if args.contains "--wrong-tests" then 4 else 3)
  IO.println <| s!"signed triangle: parents={repr actual.ret.toList}, " ++
    s!"heap={heapTuple actual.time.1}, inspections={actual.time.2.1}, tests={actual.time.2.2}"
  verify "tied triangle" triangle (fun _ => (1 : Int)) 0
    [none, some 0, some 0] 6 3 (6, 3, 11, 12, 8)
  verify "singleton" singleton (fun _ => (-7 : Int)) 0 [none] 0 0
    (0, 0, 1, 2, 2)
  verify "disconnected" disconnected disconnectedWeight 0
    [none, some 0, none, some 2] 4 2 (8, 4, 10, 16, 10)
  verify "fractional" triangle fractionalWeight 0 [none, some 0, some 1] 6 3
    (7, 3, 12, 12, 9)
  verify "duplicate occurrences" duplicateTriangle signedWeight 0
    [none, some 0, some 1] 8 4 (7, 3, 14, 12, 9)
  verify "reordered root" reorderedTriangle signedWeight 2
    [some 1, some 2, none] 6 3 (7, 3, 12, 12, 9)
  verify "isolated vertices" isolated (fun _ => (0 : Int)) 1 [none, none, none] 0 0
    (3, 4, 3, 14, 6)
  verify "zero path" zeroPath (fun _ => (0 : Int)) 0 [none, some 0, some 1] 4 2
    (5, 3, 9, 12, 8)
  verify "reversed tied adjacency" reversedTriangle (fun _ => (1 : Int)) 0
    [none, some 0, some 0] 6 3 (7, 5, 11, 16, 8)
  verify "self adjacency" loopedTriangle signedWeight 0 [none, some 0, some 1] 9 3
    (7, 3, 15, 12, 9)
  verifyFigure args

#eval main []

end PrimTests
