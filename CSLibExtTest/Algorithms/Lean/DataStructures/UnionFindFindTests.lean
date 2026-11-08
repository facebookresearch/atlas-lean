/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Find
import all CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Find
public meta import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Find
public meta import Batteries.Data.UnionFind.Basic
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Algebra.Group.Prod
public meta import Mathlib.Algebra.Group.Nat.Defs

/-! Full carried-store, rank, partition and same-run visit/write regressions. -/

open Batteries Cslib.Algorithms.Lean

namespace U081FindTests

private def verify (label : String) (self : UnionFind) (query : Nat)
    (expectedRoot : Nat) (expectedStore : Array (Nat × Nat))
    (expectedTime : Nat × Nat) : IO UnionFind := do
  let x : Fin self.size ← if h : query < self.size then pure ⟨query, h⟩
    else throw <| IO.userError s!"{label}: invalid fixture query"
  let result := UnionFind.Internal.countedFind self x
  let actualStore := result.ret.1.arr.map fun node ↦ (node.parent, node.rank)
  if result.ret.2.val.val != expectedRoot then
    throw <| IO.userError s!"{label}: root {result.ret.2.val.val} != {expectedRoot}"
  if actualStore != expectedStore then
    throw <| IO.userError s!"{label}: carried store {actualStore} != {expectedStore}"
  if result.time != expectedTime then
    throw <| IO.userError s!"{label}: events {result.time} != {expectedTime}"
  if result.ret.1.size != self.size then throw <| IO.userError s!"{label}: size"
  let canonical := self.find x
  if actualStore != canonical.1.arr.map (fun node ↦ (node.parent, node.rank)) ||
      result.ret.2.val.val != canonical.2.val.val then
    throw <| IO.userError s!"{label}: actual canonical FIND disagreement"
  for i in List.range self.size do
    if result.ret.1.rank i != self.rank i then throw <| IO.userError s!"{label}: rank {i}"
    for j in List.range self.size do
      if (result.ret.1.rootD i == result.ret.1.rootD j) != (self.rootD i == self.rootD j) then
        throw <| IO.userError s!"{label}: partition {i},{j}"
  IO.println s!"ACTUAL_COUNTED_FIND {label} ROOT {expectedRoot} EVENTS {result.time} STORE {actualStore} PAIRS {self.size * self.size}"
  pure result.ret.1

private def runCountedCases : IO Unit := do
  let singleton := UnionFind.empty.push
  let _ ← verify "singleton" singleton 0 0 #[(0, 0)] (1, 0)
  let initial := UnionFind.empty.push.push.push.push.push.push.push.push.push
  let pairs := (((initial.union! 0 1).union! 2 3).union! 4 5).union! 6 7
  let half := (pairs.union! 1 3).union! 5 7
  let chain := half.union! 3 7
  let old := #[(1, 0), (3, 1), (3, 0), (7, 2), (5, 0), (7, 1),
    (7, 0), (7, 3), (8, 0)]
  let compressed := #[(7, 0), (7, 1), (3, 0), (7, 2), (5, 0), (7, 1),
    (7, 0), (7, 3), (8, 0)]
  let saved ← verify "deep" chain 0 7 compressed (4, 3)
  let _ ← verify "root" chain 7 7 old (1, 0)
  let _ ← verify "interior" chain 1 7
    #[(1, 0), (7, 1), (3, 0), (7, 2), (5, 0), (7, 1), (7, 0), (7, 3), (8, 0)]
    (3, 2)
  let _ ← verify "repeat" saved 0 7 compressed (2, 1)
  let _ ← verify "off-path-sibling" chain 2 7
    #[(1, 0), (3, 1), (7, 0), (7, 2), (5, 0), (7, 1), (7, 0), (7, 3), (8, 0)]
    (3, 2)
  let _ ← verify "isolated" chain 8 8 old (1, 0)
  let highRank : UnionFind :=
    { arr := #[⟨0, 99⟩]
      parentD_lt := by intro i h; simp [UnionFind.parentD] at *; omega
      rankD_lt := by intro i h; simp [UnionFind.parentD] at h; omega }
  let _ ← verify "arbitrary-valid-rank" highRank 0 0 #[(0, 99)] (1, 0)
  IO.println "ACTUAL_COUNTED_FIND_CASES 8"

example : IsEmpty (Fin UnionFind.empty.size) := by
  change IsEmpty (Fin 0)
  infer_instance

#eval runCountedCases


end U081FindTests

public def main : IO Unit := U081FindTests.runCountedCases
