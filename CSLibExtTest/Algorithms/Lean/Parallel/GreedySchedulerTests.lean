/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Parallel.GreedyScheduler
public meta import CSLibExt.Algorithms.Lean.Parallel.GreedyScheduler

/-!
# Greedy scheduler tests

Closed checks: on a 15-task binary reduction tree with `p = 2`, the list schedule that runs the
two lowest-numbered ready tasks per step is proved greedy by `decide` and Graham's bound applied
to it; a schedule of a 3-task chain that idles at step 1 is proved not greedy. Executed fixtures:
for every greedy schedule produced by list scheduling (lowest-numbered ready tasks first) on four
DAGs and `p = 1, …, 5`, the bound `p T ≤ n + (p - 1) D` holds. Each run throws on a violation.
-/

namespace Cslib.Algorithms.Lean.Parallel.Brent

private def ofTable (n : ℕ) (t : List (List ℕ)) : Fin n → List (Fin n) := fun v =>
  (t.getD v.val []).filterMap fun u => if h : u < n then some ⟨u, h⟩ else none

/-- A schedule from a table of times, with capacity checked on the steps it uses. -/
private def ofTimes {n p : ℕ} (G : Dag n) (times : List ℕ) (T : ℕ)
    (hT : ∀ v : Fin n, times.getD v.val 0 < T)
    (prec : ∀ v, ∀ u ∈ G.preds v, times.getD u.val 0 < times.getD v.val 0)
    (cap : ∀ t < T, (Finset.univ.filter fun v : Fin n => times.getD v.val 0 = t).card ≤ p) :
    Schedule G p where
  time v := times.getD v.val 0
  prec := prec
  cap t := by
    by_cases ht : t < T
    · exact cap t ht
    · have : (Finset.univ.filter fun v : Fin n => times.getD v.val 0 = t) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun v _ h => ht (h ▸ hT v)
      rw [this, Finset.card_empty]; exact Nat.zero_le _

private def tree : Dag 15 := ⟨ofTable 15 [[], [], [], [], [], [], [], [], [0, 1], [2, 3], [4, 5],
  [6, 7], [8, 9], [10, 11], [12, 13]], by decide⟩

private def treeTimes : List ℕ := [0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7]

private def treeGreedy : Schedule tree 2 :=
  ofTimes tree treeTimes 8 (by decide) (by decide) (by decide)

example : treeGreedy.Greedy := by decide

example : 2 * treeGreedy.length ≤ 15 + 2 * span tree := treeGreedy.greedy_length (by decide)

example : 2 * treeGreedy.length ≤ 15 + (2 - 1) * span tree :=
  treeGreedy.greedy_length_le (by decide)

private def chain : Dag 3 := ⟨ofTable 3 [[], [0], [1]], by decide⟩

/-- Idles at step 1 although task 1 is ready. -/
private def chainIdle : Schedule chain 1 := ofTimes chain [0, 2, 3] 4 (by decide) (by decide)
  (by decide)

example : ¬ chainIdle.Greedy := by decide

/-- List scheduling: each step runs the `p` lowest-numbered ready tasks. -/
private meta def listTimes {n : ℕ} (G : Dag n) (p : ℕ) : List ℕ := Id.run do
  let mut times : Array (Option ℕ) := Array.replicate n none
  let mut t := 0
  while times.any (·.isNone) && t ≤ n do
    let ready := (List.finRange n).filter fun v => times[v.val]!.isNone &&
      (G.preds v).all fun u => match times[u.val]! with | some s => s < t | none => false
    for v in ready.take p do times := times.set! v.val (some t)
    t := t + 1
  return times.toList.map (·.getD 0)

private def layered : Dag 12 := ⟨ofTable 12 ((List.range 12).map fun i =>
  if i < 4 then [] else (List.range 4).map fun j => (i / 4 - 1) * 4 + j), by decide⟩

private def chain8 : Dag 8 :=
  ⟨ofTable 8 ((List.range 8).map fun i => if i = 0 then [] else [i - 1]), by decide⟩

private def antichain : Dag 8 := ⟨fun _ => [], by decide⟩

private meta def check {n : ℕ} (name : String) (G : Dag n) : IO Unit := do
  for p in [1, 2, 3, 4, 5] do
    let times := listTimes G p
    let T := times.foldl max 0 + 1
    let D := span G
    let load := fun t => (times.filter (· == t)).length
    -- greedy: whenever a task is ready and waits, the step is full
    for t in List.range T do
      for v in List.finRange n do
        let ready := t < times.getD v.val 0 && (G.preds v).all fun u => times.getD u.val 0 < t
        if ready && load t != p then throw (IO.userError s!"{name}, p = {p}: not greedy at {t}")
    unless p * T ≤ n + (p - 1) * D do throw (IO.userError s!"{name}, p = {p}: T = {T}, D = {D}")
    if p == 2 then IO.println s!"{name}: n = {n}, span {D}; greedy with p = 2: {T} steps, {times}"

#eval do
  check "tree" tree
  check "layered" layered
  check "chain" chain8
  check "antichain" antichain
  IO.println "list schedules on four DAGs, p = 1..5: greedy, and p T ≤ n + (p - 1) D"

#print axioms Schedule.greedy_length
#print axioms Schedule.greedy_length_le
#print axioms Schedule.incomplete_lt_depth

end Cslib.Algorithms.Lean.Parallel.Brent
