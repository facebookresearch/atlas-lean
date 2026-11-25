/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind
public meta import CSLibExt.Algorithms.Lean.DataStructures.UnionFind

/-!
# Runtime tests for persistent union-find forests

Three carried traces check every ordered pair and returned root against flat whole-class
labels. Literal partitions, a saved snapshot, reversed union directions, a singleton, and
two deliberately wrong legal results test the observer. Labels name classes, not expected
representatives. This complements direct contract proofs and downstream Kruskal runtime tests.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.UnionFindRuntimeTests

open UnionFind

private def discrete (n : Nat) : Forest n where
  parent i := i
  depth _ := 0
  parent_lt _ h := False.elim (h rfl)

private def vertices : List (Fin 5) := [0, 1, 2, 3, 4]

private def rootVector (forest : Forest 5) : List Nat :=
  vertices.map (fun i => (find forest i).val)

-- Canonical class labels name partitions, not production representatives.
private def mergeLabels (labels : List Nat) (x y : Fin 5) : List Nat :=
  let a := labels[x.val]!
  let b := labels[y.val]!
  labels.map (fun label => if label == a || label == b then min a b else label)

-- Visit every pair and root even after a mismatch, retaining full diagnostics.
private def inspect (forest : Forest 5) (labels : List Nat) :
    Array String × Nat × Nat := Id.run do
  let mut errors : Array String := #[]
  let mut pairs := 0
  let mut roots := 0
  if labels.length != 5 then
    errors := errors.push "expected five class labels"
  for i in vertices do
    let ri := find forest i
    roots := roots + 1
    if forest.parent ri != ri then
      errors := errors.push s!"nonroot result at {i.val}: {ri.val}"
    for j in vertices do
      let actual := ri == find forest j
      let expected := labels[i.val]! == labels[j.val]!
      pairs := pairs + 1
      if actual != expected then
        errors := errors.push s!"pair ({i.val},{j.val}): got={actual}, want={expected}"
  return (errors, pairs, roots)

private def observe (label : String) (forest : Forest 5) (labels : List Nat) :
    IO (Nat × Nat) := do
  let (errors, pairs, roots) := inspect forest labels
  unless errors.isEmpty do
    throw <| IO.userError <| s!"partition mismatch: {label}, " ++
      s!"roots={rootVector forest}, expected={labels}, mismatches={errors}"
  IO.println s!"PASS {label}: roots={rootVector forest}, expected={labels}"
  return (pairs, roots)

private def runTrace (label : String) (operations : List (Fin 5 × Fin 5)) :
    IO (Array (Forest 5) × Nat × Nat) := do
  let mut forest := discrete 5
  let mut labels := [0, 1, 2, 3, 4]
  let mut history := #[forest]
  let mut prefixIndex := 0
  let initial ← observe s!"trace {label} prefix={prefixIndex}" forest labels
  let mut pairs := initial.1
  let mut roots := initial.2
  for (x, y) in operations do
    forest := union forest x y
    labels := mergeLabels labels x y
    prefixIndex := prefixIndex + 1
    history := history.push forest
    let counts ← observe s!"trace {label} prefix={prefixIndex}" forest labels
    pairs := pairs + counts.1
    roots := roots + counts.2
  unless prefixIndex == operations.length && history.size == operations.length + 1 do
    throw <| IO.userError "carried prefix count mismatch"
  return (history, pairs, roots)

private def rejectState (label : String) (baseline wrong : Forest 5)
    (labels : List Nat) : IO Unit := do
  let _ ← observe s!"baseline {label}" baseline labels
  let (errors, pairs, roots) := inspect wrong labels
  unless !errors.isEmpty && pairs == 25 && roots == 5 do
    throw <| IO.userError s!"wrong legal result accepted: {label}"
  IO.println <| s!"REJECT {label}: roots={rootVector wrong}, " ++
    s!"expected={labels}, mismatches={errors}"

private def runTests : IO Unit := do
  let chain : List (Fin 5 × Fin 5) := [(0, 1), (1, 2), (2, 3), (3, 4)]
  let bridge : List (Fin 5 × Fin 5) := [(0, 1), (2, 3), (0, 2), (4, 1)]
  let noOps : List (Fin 5 × Fin 5) := [(0, 0), (0, 1), (1, 0), (2, 3), (0, 1)]
  let h1 ← runTrace "chain" chain
  let h2 ← runTrace "bridge" bridge
  let h3 ← runTrace "no-ops" noOps
  let observations := h1.1.size + h2.1.size + h3.1.size
  let transitions := chain.length + bridge.length + noOps.length
  let pairs := h1.2.1 + h2.2.1 + h3.2.1
  let roots := h1.2.2 + h2.2.2 + h3.2.2
  unless transitions == 13 && observations == 16 && pairs == 400 && roots == 80 do
    throw <| IO.userError "trace totals mismatch"
  IO.println "TRACES passed=3, transitions=13, observations=16, pairs=400, roots=80"

  let some saved := h2.1[2]? | throw <| IO.userError "missing saved bridge snapshot"
  let some joined := h2.1[3]? | throw <| IO.userError "missing bridge class merge"
  let some complete := h2.1[4]? | throw <| IO.userError "missing final bridge merge"
  let twoClasses := [0, 0, 2, 2, 4]
  let firstFour := [0, 0, 0, 0, 4]
  let _ ← observe "anchor discrete" (discrete 5) [0, 1, 2, 3, 4]
  let _ ← observe "anchor two classes" saved twoClasses
  let _ ← observe "anchor first four" joined firstFour
  let _ ← observe "anchor all joined" complete [0, 0, 0, 0, 0]
  let _ ← observe "saved snapshot after later unions" saved twoClasses
  IO.println "ANCHORS passed=4, saved-snapshot=1 (extra check)"

  let left := union (discrete 5) 0 1
  let right := union (discrete 5) 1 0
  let samePartition := [0, 0, 2, 3, 4]
  let _ ← observe "direction forward" left samePartition
  let _ ← observe "direction reverse" right samePartition
  unless find left 0 != find right 0 do
    throw <| IO.userError "direction fixture did not change representative"
  IO.println "DIRECTION same-partition=2, actual-representatives-differ=true"

  let singleton := discrete 1
  unless find singleton 0 == 0 do
    throw <| IO.userError "singleton root mismatch"
  IO.println s!"SINGLETON passed=1, roots=[{(find singleton 0).val}]"

  rejectState "skip required merge" joined saved firstFour
  rejectState "merge isolated vertex instead" joined (union saved 0 4) firstFour
  IO.println "CONTROLS rejected=2, baselines=2"

#eval runTests

end Cslib.Algorithms.Lean.UnionFindRuntimeTests
