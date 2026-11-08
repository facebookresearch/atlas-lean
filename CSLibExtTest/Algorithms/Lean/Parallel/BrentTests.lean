/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Parallel.Brent
public meta import CSLibExt.Algorithms.Lean.Parallel.Brent

/-!
# Brent's theorem tests

Executed fixtures: on a chain, an antichain, a binary reduction tree and a layered DAG, for
`p = 1, …, 5`, Brent's level schedule is checked to respect precedence and capacity, its length
`T` to satisfy `p T ≤ n + (p - 1) D` and both laws (`n ≤ p T`, `D ≤ T`), and the tabulated
depths to agree with `depth`. Each run throws on a violation. Closed checks instantiate the
theorems.
-/

namespace Cslib.Algorithms.Lean.Parallel.Brent

/-- A DAG from a predecessor table, dropping out-of-range entries. -/
private def ofTable (n : ℕ) (t : List (List ℕ)) : Fin n → List (Fin n) := fun v =>
  (t.getD v.val []).filterMap fun u => if h : u < n then some ⟨u, h⟩ else none

private def chain : Dag 8 := ⟨ofTable 8 ((List.range 8).map fun i => if i = 0 then [] else [i - 1]),
  by decide⟩

private def antichain : Dag 8 := ⟨fun _ => [], by decide⟩

/-- Leaves `0..7`, then pairwise sums up to the root `14`. -/
private def tree : Dag 15 := ⟨ofTable 15 [[], [], [], [], [], [], [], [], [0, 1], [2, 3], [4, 5],
  [6, 7], [8, 9], [10, 11], [12, 13]], by decide⟩

/-- Three wide layers with all-to-all dependencies between consecutive layers. -/
private def layered : Dag 12 := ⟨ofTable 12 ((List.range 12).map fun i =>
  if i < 4 then [] else (List.range 4).map fun j => (i / 4 - 1) * 4 + j), by decide⟩

private meta def check {n : ℕ} (name : String) (G : Dag n) : IO Unit := do
  for p in [1, 2, 3, 4, 5] do
    if hp : 1 ≤ p then
      let S := levelSchedule G hp
      let T := S.length
      let D := span G
      let times := (List.finRange n).map S.time
      for v in List.finRange n do
        for u in G.preds v do
          unless S.time u < S.time v do throw (IO.userError s!"{name}: precedence broken")
      for t in List.range T do
        unless (times.filter (· == t)).length ≤ p do throw (IO.userError s!"{name}: over capacity")
      unless p * T ≤ n + (p - 1) * D && n ≤ p * T && D ≤ T do
        throw (IO.userError s!"{name}, p = {p}: T = {T}, n = {n}, D = {D}")
      if p == 2 then IO.println s!"{name}: n = {n}, span {D}; p = 2: {T} steps, times {times}"
  unless (List.finRange n).all fun v => (depthTable G).getD v.val 0 == depth G v do
    throw (IO.userError s!"{name}: depth table mismatch")

#eval do
  check "chain" chain
  check "antichain" antichain
  check "tree" tree
  check "layered" layered
  IO.println "all four DAGs, p = 1..5: valid schedules with p T ≤ n + (p - 1) D, n ≤ p T, D ≤ T"

/-! Closed checks -/

example : ∃ S : Schedule tree 4, 4 * S.length ≤ 15 + 3 * span tree ∧
    ∀ S' : Schedule tree 4, 15 ≤ 4 * S'.length ∧ span tree ≤ S'.length :=
  brent tree (by decide)

#print axioms brent
#print axioms levelSchedule_length
#print axioms Schedule.work_le
#print axioms Schedule.span_le
#print axioms getD_depthTable

end Cslib.Algorithms.Lean.Parallel.Brent
