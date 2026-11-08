/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.ConnectedComponents
public meta import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.ConnectedComponents
public meta import Batteries.Data.UnionFind.Basic
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Algebra.Group.Prod
public meta import Mathlib.Algebra.Group.Nat.Defs

open Batteries Batteries.UnionFind Cslib.Algorithms.Lean

public meta section

private def verifyCountCase (label : String) (n : Nat) (edges : List (Fin n × Fin n))
    (expectedTime : Nat × Nat × Nat) (expectedCells : Array (Nat × Nat))
    (expectedRoots : List Nat) : IO Unit := do
  let result := connectedComponents n edges
  let cells := result.ret.val.arr.map fun node ↦ (node.parent, node.rank)
  let roots := (List.range n).map result.ret.val.rootD
  if result.time != expectedTime then
    throw <| IO.userError s!"{label}: expected counts {expectedTime}, actual {result.time}"
  if cells != expectedCells then
    throw <| IO.userError s!"{label}: expected full store {expectedCells}, actual {cells}"
  if roots != expectedRoots || result.ret.val.size != n then
    throw <| IO.userError s!"{label}: expected roots {expectedRoots}, actual {roots}"
  for i in List.range n do
    for j in List.range n do
      if (result.ret.val.rootD i == result.ret.val.rootD j) !=
          (expectedRoots[i]! == expectedRoots[j]!) then
        throw <| IO.userError s!"{label}: actual ordered partition at {i},{j}"
  IO.println s!"U080_CASE {label} COUNTS {result.time} STORE {cells} ROOTS {roots} PAIRS {n*n}"

private def runCountCases (mode : String) : IO Unit := do
  let figure : List (Fin 10 × Fin 10) :=
    [(1, 3), (4, 5), (0, 2), (7, 8), (0, 1), (5, 6), (1, 2)]
  let ft := if mode == "wrong-allocation" then (9, 14, 6)
    else if mode == "wrong-guard" then (10, 7, 6)
    else if mode == "wrong-union" then (10, 14, 7) else (10, 14, 6)
  verifyCountCase "CLRS_FIGURE19_1" 10 figure ft
    #[(2,0),(3,0),(3,1),(3,2),(5,0),(5,1),(5,0),(8,0),(8,1),(9,0)]
    [3,3,3,3,5,5,5,8,8,9]
  verifyCountCase "CLRS_DUPLICATE_COMPRESSION" 10 (figure ++ [(0,1)]) (10,16,6)
    (if mode == "wrong-compression" then
      #[(2,0),(3,0),(3,1),(3,2),(5,0),(5,1),(5,0),(8,0),(8,1),(9,0)] else
      #[(3,0),(3,0),(3,1),(3,2),(5,0),(5,1),(5,0),(8,0),(8,1),(9,0)])
    [3,3,3,3,5,5,5,8,8,9]
  verifyCountCase "EMPTY" 0 [] (0,0,0) #[] []
  verifyCountCase "ISOLATED" 3 [] (3,0,0) #[(0,0),(1,0),(2,0)] [0,1,2]
  verifyCountCase "SINGLETON" 1 [] (1,0,0) #[(0,0)] [0]
  verifyCountCase "SINGLETON_LOOP" 1 [(0,0)] (1,2,0) #[(0,0)] [0]
  verifyCountCase "REVERSED_DUPLICATE_LOOP" 3 [(0,1),(1,0),(1,1)]
    (3,6,1) #[(1,0),(1,1),(2,0)] [1,1,2]
  verifyCountCase "TRIANGLE" 3 [(0,1),(1,2),(2,0)]
    (3,6,2) #[(1,0),(1,1),(1,0)] [1,1,1]
  verifyCountCase "TRIANGLE_OTHER_ORDER" 3 [(2,0),(1,2),(0,1)]
    (3,6,2) #[(0,1),(0,0),(0,0)] [0,0,0]
  verifyCountCase "SELF_LOOPS_ONLY" 3 [(0,0),(2,2),(0,0)]
    (3,6,0) #[(0,0),(1,0),(2,0)] [0,1,2]
  verifyCountCase "RANK_CHAIN" 4 [(0,1),(2,3),(0,2)]
    (4,6,3) #[(1,0),(3,1),(3,0),(3,2)] [3,3,3,3]
  verifyCountCase "RANK_CHAIN_TRUE_GUARD_COMPRESSION" 4 [(0,1),(2,3),(0,2),(0,0)]
    (4,8,3) #[(3,0),(3,1),(3,0),(3,2)] [3,3,3,3]
  IO.println "U080_SUITE_COMPLETE 12 cases"


#eval runCountCases "good"

end
