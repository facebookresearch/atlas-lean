/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Trie.Delete
public meta import CSLibExt.Algorithms.Lean.DataStructures.Trie
public meta import CSLibExt.Algorithms.Lean.DataStructures.Trie.Delete

/-!
# Runtime tests for finite tries

Four carried operation traces compare public lookups and complete unordered entries with
a flat map keyed by whole lists. Literal anchors, a saved snapshot, different entry orders,
and deliberately wrong legal returned states check the observer itself. These finite tests
complement the existing deterministic-order proofs; they do not prove universal correctness.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.TrieRuntimeTests

private def modelLookup (expected : List (List Nat × Nat)) (key : List Nat) : Option Nat :=
  (expected.find? (fun entry => entry.1 == key)).map Prod.snd

private def probes : List (List Nat) := [[], [0], [0, 0], [0, 1], [1], [2], [9]]

private def probesAgree (trie : Trie Nat Nat) (expected : List (List Nat × Nat)) : Bool :=
  probes.all (fun key => trie.lookup key == modelLookup expected key)

private def entriesAgree (trie : Trie Nat Nat) (expected : List (List Nat × Nat)) : Bool :=
  let actual := trie.entries
  decide (actual.map Prod.fst).Nodup && decide (expected.map Prod.fst).Nodup &&
    actual.length == expected.length &&
    actual.all (fun entry => expected.contains entry) &&
    expected.all (fun entry => actual.contains entry)

private def accepts (trie : Trie Nat Nat) (expected : List (List Nat × Nat)) : Bool :=
  probesAgree trie expected && entriesAgree trie expected

private def observe (label : String) (trie : Trie Nat Nat)
    (expected : List (List Nat × Nat)) : IO Unit := do
  unless accepts trie expected do
    throw <| IO.userError
      s!"observation mismatch: {label}, actual={trie.entries}, expected={expected}"
  IO.println s!"PASS {label}: entries={trie.entries}"

private def modelUpdate (expected : List (List Nat × Nat))
    (operation : List Nat × Option Nat) : List (List Nat × Nat) :=
  let rest := expected.filter (fun entry => entry.1 != operation.1)
  match operation.2 with
  | none => rest
  | some value => (operation.1, value) :: rest

private def step (trie : Trie Nat Nat) (operation : List Nat × Option Nat) : Trie Nat Nat :=
  match operation.2 with
  | none => trie.delete operation.1
  | some value => trie.insert operation.1 value

private def runTrace (label : String) (operations : List (List Nat × Option Nat)) :
    IO (Array (Trie Nat Nat)) := do
  let mut trie : Trie Nat Nat := Trie.empty
  let mut expected : List (List Nat × Nat) := []
  let mut history := #[trie]
  let mut prefixIndex := 0
  observe s!"trace {label} prefix={prefixIndex}" trie expected
  for operation in operations do
    trie := step trie operation
    expected := modelUpdate expected operation
    prefixIndex := prefixIndex + 1
    history := history.push trie
    observe s!"trace {label} prefix={prefixIndex}" trie expected
  unless history.size == operations.length + 1 do
    throw <| IO.userError "carried prefix count mismatch"
  return history

private def rejectState (label : String) (baseline wrong : Trie Nat Nat)
    (expected : List (List Nat × Nat)) : IO Unit := do
  observe s!"baseline {label}" baseline expected
  if accepts wrong expected then
    throw <| IO.userError s!"wrong legal state accepted: {label}"
  IO.println s!"REJECT {label}: entries={wrong.entries}"
  IO.println <| s!"CONTROL {label}: probes={probesAgree wrong expected}, " ++
    s!"full-entries={entriesAgree wrong expected}"

private def runTests : IO Unit := do
  let rootOverwrite : List (List Nat × Option Nat) :=
    [([], some 0), ([0], some 0), ([0], some 7), ([], none), ([], some 7)]
  let prefixRetention : List (List Nat × Option Nat) :=
    [([0], some 0), ([0, 0], some 7), ([0, 1], some 0), ([0], none), ([0], some 7)]
  let extensionAndMiss : List (List Nat × Option Nat) :=
    [([0], some 0), ([0, 0], some 7), ([0, 1], some 0), ([1], some 7),
      ([0, 0], none), ([2], none)]
  let reverseOrderReinsert : List (List Nat × Option Nat) :=
    [([1], some 7), ([0, 1], some 0), ([0, 0], some 7), ([0], some 0),
      ([0, 0], none), ([0, 0], some 7)]
  let h1 ← runTrace "root-overwrite" rootOverwrite
  let h2 ← runTrace "prefix-retention" prefixRetention
  let some saved := h2[3]? | throw <| IO.userError "missing saved snapshot"
  let h3 ← runTrace "extension-and-miss" extensionAndMiss
  let h4 ← runTrace "reverse-order-reinsert" reverseOrderReinsert
  let observations := h1.size + h2.size + h3.size + h4.size
  let transitions := rootOverwrite.length + prefixRetention.length +
    extensionAndMiss.length + reverseOrderReinsert.length
  unless transitions == 22 && observations == 26 && observations * probes.length == 182 do
    throw <| IO.userError "trace totals mismatch"
  IO.println "TRACES passed=4, transitions=22, observations=26, probes=182"

  let some overwritten := h1[3]? | throw <| IO.userError "missing overwrite"
  let some beforeOverwrite := h1[2]? | throw <| IO.userError "missing old overwrite value"
  let some prefixDeleted := h2[4]? | throw <| IO.userError "missing prefix deletion"
  let some extensionDeleted := h3[5]? | throw <| IO.userError "missing extension deletion"
  let overwriteMap : List (List Nat × Nat) := [([], 0), ([0], 7)]
  let prefixDeletedMap : List (List Nat × Nat) := [([0, 0], 7), ([0, 1], 0)]
  let extensionDeletedMap : List (List Nat × Nat) := [([0], 0), ([0, 1], 0), ([1], 7)]
  let savedMap : List (List Nat × Nat) := [([0], 0), ([0, 0], 7), ([0, 1], 0)]
  observe "anchor overwrite" overwritten overwriteMap
  observe "anchor prefix deletion" prefixDeleted prefixDeletedMap
  observe "anchor extension deletion" extensionDeleted extensionDeletedMap
  observe "saved snapshot after later updates" saved savedMap
  IO.println "ANCHORS passed=3, saved-snapshot=1 (extra check)"

  let some orderLeft := h3[4]? | throw <| IO.userError "missing first insertion order"
  let some orderRight := h4[4]? | throw <| IO.userError "missing reverse insertion order"
  let orderMap : List (List Nat × Nat) :=
    [([0], 0), ([0, 0], 7), ([0, 1], 0), ([1], 7)]
  observe "equivalent map first order" orderLeft orderMap
  observe "equivalent map reverse order" orderRight orderMap
  unless orderLeft.entries != orderRight.entries do
    throw <| IO.userError "entry-order fixture no longer produces distinct lists"
  IO.println "ORDER same-map=2, actual-lists-differ=true"

  rejectState "skip overwrite" overwritten beforeOverwrite overwriteMap
  rejectState "skip present deletion" prefixDeleted saved prefixDeletedMap
  rejectState "delete live extension too" prefixDeleted
    (prefixDeleted.delete [0, 0]) prefixDeletedMap
  let empty : Trie Nat Nat := Trie.empty
  let ghost := empty.insert [9, 9] 7
  unless probesAgree ghost [] && !entriesAgree ghost [] do
    throw <| IO.userError "ghost did not separate probes from complete entries"
  rejectState "ghost entry" empty ghost []
  IO.println "CONTROLS rejected=4, baselines=4, ghost-probes-agree=true"

#eval runTests

end Cslib.Algorithms.Lean.TrieRuntimeTests
