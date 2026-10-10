/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Union
public meta import Batteries.Data.UnionFind.Basic
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Algebra.Group.Nat.Defs
public meta import Mathlib.Algebra.Group.Prod
public meta import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Find
public meta import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Union

import all CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Union

/-! Actual canonical carried stores and the same-run private source-counted LINK/UNION. -/

open Batteries Cslib.Algorithms.Lean

private def verifyLink (label : String) (self : UnionFind) (x y : Nat)
    (expected : Array (Nat × Nat)) (events : Nat × Nat × Nat) : IO Unit := do
  let fx : Fin self.size ← if h : x < self.size then pure ⟨x, h⟩
    else throw <| IO.userError s!"{label}: allocated x"
  let fy : Fin self.size ← if h : y < self.size then pure ⟨y, h⟩
    else throw <| IO.userError s!"{label}: allocated y"
  if fx.val != x || fy.val != y then throw <| IO.userError s!"{label}: input identities"
  if self.parent fx != fx then throw <| IO.userError s!"{label}: source x is not a root"
  if hy : self.parent fy = fy then
    let actual := Batteries.UnionFind.LinkInternal.countedLinkAux self.arr fx fy
    let after := actual.ret.map fun node ↦ (node.parent, node.rank)
    if after != expected then throw <| IO.userError s!"{label}: store {after} != {expected}"
    if actual.time != events then
      throw <| IO.userError s!"{label}: events {actual.time} != {events}"
    let canonical := self.link fx fy hy
    if after != (canonical.arr.map fun node ↦ (node.parent, node.rank)) then
      throw <| IO.userError s!"{label}: canonical carried array"
    if actual.ret.size != self.size then throw <| IO.userError s!"{label}: size"
    for i in List.range self.size do
      for j in List.range self.size do
        let old := self.rootD i == self.rootD j
        let throughXY := (self.rootD i == x) && (self.rootD j == y)
        let throughYX := (self.rootD i == y) && (self.rootD j == x)
        if (canonical.rootD i == canonical.rootD j) != (old || throughXY || throughYX) then
          throw <| IO.userError s!"{label}: exact two-class partition {i},{j}"
    IO.println s!"ACTUAL_U082_LINK {label} EVENTS {actual.time} STORE {after}"
  else
    throw <| IO.userError s!"{label}: source y is not a root"
private def runCostCases : IO Unit := do
  let separate := UnionFind.empty.push.push
  verifyLink "tied-roots" separate 0 1 #[(1, 0), (1, 1)] (2, 1, 1)
  verifyLink "equal-index-extension" separate 0 0 #[(0, 0), (1, 0)] (0, 0, 0)
  let four := UnionFind.empty.push.push.push.push
  let higher := four.union! 0 1
  verifyLink "higher-first" higher 1 2 #[(1, 0), (1, 1), (1, 0), (3, 0)] (1, 1, 0)
  verifyLink "higher-second" higher 2 1 #[(1, 0), (1, 1), (1, 0), (3, 0)] (2, 1, 0)
  let twoTrees := higher.union! 2 3
  verifyLink "nonzero-tie" twoTrees 1 3 #[(1, 0), (3, 1), (3, 0), (3, 2)] (2, 1, 1)
  verifyLink "reversed-nonzero-tie" twoTrees 3 1
    #[(1, 0), (1, 2), (3, 0), (1, 1)] (2, 1, 1)
  let nine := UnionFind.empty.push.push.push.push.push.push.push.push.push
  let pairs := (((nine.union! 0 1).union! 2 3).union! 4 5).union! 6 7
  let half := (pairs.union! 1 3).union! 5 7
  let chain := half.union! 3 7
  verifyLink "full-store-isolated-merge" chain 7 8
    #[(1, 0), (3, 1), (3, 0), (7, 2), (5, 0), (7, 1), (7, 0), (7, 3), (7, 0)]
    (1, 1, 0)
  let highRank : UnionFind :=
    { arr := #[⟨0, 99⟩]
      parentD_lt := by intro i h; simp [UnionFind.parentD] at *; omega
      rankD_lt := by intro i h; simp [UnionFind.parentD] at h; omega }
  verifyLink "arbitrary-valid-rank" highRank 0 0 #[(0, 99)] (0, 0, 0)
  IO.println "ACTUAL_U082_LINK_CASES 8"

example : IsEmpty (Fin UnionFind.empty.size) := by
  change IsEmpty (Fin 0)
  infer_instance

private def verifyUnion (label : String) (self : UnionFind) (x y : Nat)
    (expected : Array (Nat × Nat)) (events : (Nat × Nat) × (Nat × Nat × Nat)) :
    IO Unit := do
  let fx : Fin self.size ← if h : x < self.size then pure ⟨x, h⟩
    else throw <| IO.userError s!"{label}: allocated x"
  let fy : Fin self.size ← if h : y < self.size then pure ⟨y, h⟩
    else throw <| IO.userError s!"{label}: allocated y"
  let actual := Batteries.UnionFind.LinkInternal.countedUnion self fx fy
  let store := actual.ret.map fun node ↦ (node.parent, node.rank)
  if store != expected then throw <| IO.userError s!"{label}: carried store {store}"
  if actual.time != events then
    throw <| IO.userError s!"{label}: events {actual.time} != {events}"
  let canonical := self.union fx fy
  if store != canonical.arr.map (fun node ↦ (node.parent, node.rank)) then
    throw <| IO.userError s!"{label}: direct canonical UNION erasure"
  if actual.ret.size != self.size then throw <| IO.userError s!"{label}: allocated size"
  if actual.time.1.1 != actual.time.1.2 + 2 then
    throw <| IO.userError s!"{label}: two actual FIND visits/writes"
  for i in List.range self.size do
    for j in List.range self.size do
      let old := self.rootD i == self.rootD j
      let forward := (self.rootD i == self.rootD x) && (self.rootD j == self.rootD y)
      let backward := (self.rootD i == self.rootD y) && (self.rootD j == self.rootD x)
      if (canonical.rootD i == canonical.rootD j) != (old || forward || backward) then
        throw <| IO.userError s!"{label}: allocated class merge {i},{j}"
  IO.println s!"ACTUAL_U082_COUNTED_UNION {label} EVENTS {actual.time} STORE {store}"

private def runUnionCases : IO Unit := do
  let nine := UnionFind.empty.push.push.push.push.push.push.push.push.push
  let pairs := (((nine.union! 0 1).union! 2 3).union! 4 5).union! 6 7
  let half := (pairs.union! 1 3).union! 5 7
  let chain := half.union! 3 7
  verifyUnion "overlapping-carried-find" chain 0 1
    #[(7, 0), (7, 1), (3, 0), (7, 2), (5, 0), (7, 1), (7, 0), (7, 3), (8, 0)]
    ((6, 4), (0, 0, 0))
  verifyUnion "singleton-same-class-extension" UnionFind.empty.push 0 0
    #[(0, 0)] ((2, 0), (0, 0, 0))
  verifyUnion "distinct-rank-zero" UnionFind.empty.push.push 0 1
    #[(1, 0), (1, 1)] ((2, 0), (2, 1, 1))
  let four := UnionFind.empty.push.push.push.push
  let higher := four.union! 0 1
  verifyUnion "higher-first" higher 1 2
    #[(1, 0), (1, 1), (1, 0), (3, 0)] ((2, 0), (1, 1, 0))
  verifyUnion "higher-second" higher 2 1
    #[(1, 0), (1, 1), (1, 0), (3, 0)] ((2, 0), (2, 1, 0))
  let twoTrees := higher.union! 2 3
  verifyUnion "nonroot-tied-classes" twoTrees 0 2
    #[(1, 0), (3, 1), (3, 0), (3, 2)] ((4, 2), (2, 1, 1))
  verifyUnion "deep-isolated-merge" chain 0 8
    #[(7, 0), (7, 1), (3, 0), (7, 2), (5, 0), (7, 1), (7, 0), (7, 3), (7, 0)]
    ((5, 3), (1, 1, 0))
  verifyUnion "same-query-second-find-still-writes" chain 0 0
    #[(7, 0), (7, 1), (3, 0), (7, 2), (5, 0), (7, 1), (7, 0), (7, 3), (8, 0)]
    ((6, 4), (0, 0, 0))
  IO.println "ACTUAL_U082_COUNTED_UNION_CASES 8"

/-- Actual canonical UNION, with overlapping paths and both dependent carried FIND results. -/
private def runCarriedCase : IO Unit := do
  let initial := UnionFind.empty.push.push.push.push.push.push.push.push.push
  let pairs := (((initial.union! 0 1).union! 2 3).union! 4 5).union! 6 7
  let half := (pairs.union! 1 3).union! 5 7
  let chain := half.union! 3 7
  let before := chain.arr.map fun node ↦ (node.parent, node.rank)
  if before != #[(1, 0), (3, 1), (3, 0), (7, 2), (5, 0), (7, 1),
      (7, 0), (7, 3), (8, 0)] then
    throw <| IO.userError s!"initial full store: {before}"
  let x : Fin chain.size ← if h : 0 < chain.size then pure ⟨0, h⟩
    else throw <| IO.userError "allocated first query"
  let y : Fin chain.size ← if h : 1 < chain.size then pure ⟨1, h⟩
    else throw <| IO.userError "allocated second query"
  let first := chain.find x
  let y₁ : Fin first.1.size := ⟨y.val, by rw [UnionFind.find_size]; exact y.isLt⟩
  let second := first.1.find y₁
  let result := chain.union x y
  let expected := #[(7, 0), (7, 1), (3, 0), (7, 2), (5, 0), (7, 1),
    (7, 0), (7, 3), (8, 0)]
  let after := result.arr.map fun node ↦ (node.parent, node.rank)
  if after != expected || result.size != 9 then
    throw <| IO.userError s!"actual UNION full carried store: {after}"
  if first.2.val.val != 7 || second.2.val.val != 7 then
    throw <| IO.userError "actual FIND returned roots"
  if (first.1.arr.map fun node ↦ (node.parent, node.rank)) != expected ||
      (second.1.arr.map fun node ↦ (node.parent, node.rank)) != expected then
    throw <| IO.userError "both actual FIND carried stores"
  let discarded := (chain.find y).1.arr.map fun node ↦ (node.parent, node.rank)
  if discarded == after || discarded[0]!.1 != 1 then
    throw <| IO.userError "original-store second FIND must distinguish discarded compression"
  for i in List.range 9 do
    if result.rank i != chain.rank i then throw <| IO.userError s!"rank frame {i}"
    for j in List.range 9 do
      if (result.rootD i == result.rootD j) != (chain.rootD i == chain.rootD j) then
        throw <| IO.userError s!"same-class partition {i},{j}"
  IO.println s!"ACTUAL_U082_CARRIED_UNION ROOTS 7,7 STORE {after} PAIRS 81"

private def runAllCases : IO Unit := do
  runCostCases
  runUnionCases
  runCarriedCase

#eval runAllCases
