/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.LongestCommonSubsequence
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.LongestCommonSubsequence

/-!
# Runtime tests for longest common subsequence witnesses

All binary list pairs through length three check the returned length and witness.
Independent positional-subsequence enumeration supplies the optimum; a greedy scan
checks witness order and multiplicity. Different tied optima are accepted.
This is finite executable coverage, with shared LCS mathematics.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.LongestCommonSubsequenceRuntimeTests

-- Each position independently extends or leaves each subsequence, retaining duplicates.
private def positionalSubsequences (source : List Nat) : List (List Nat) :=
  source.foldl (fun sequences value =>
    sequences ++ sequences.map (fun sequence => sequence ++ [value])) [[]]

private def exhaustiveOptimum (left right : List Nat) : Nat :=
  let rightSequences := positionalSubsequences right
  ((positionalSubsequences left).filter (fun sequence => rightSequences.contains sequence)).foldl
    (fun best sequence => max best sequence.length) 0

-- Greedily consume the next witness value while scanning the source in order.
private def greedySubsequence (source witness : List Nat) : Bool := Id.run do
  let expected := witness.toArray
  let mut cursor := 0
  for value in source do
    if expected[cursor]? == some value then cursor := cursor + 1
  return cursor == expected.size

-- Keep all four conjuncts separate, including for wrong legal results.
private def inspect (left right : List Nat) (result : Nat × List Nat)
    (optimum : Nat) : List Bool :=
  [greedySubsequence left result.2, greedySubsequence right result.2,
    result.1 == result.2.length, result.1 == optimum]

private def details (left right : List Nat) (result : Nat × List Nat)
    (optimum : Nat) : String :=
  s!"left={left}, right={right}, reported-length={result.1}, witness={result.2}, " ++
    s!"witness-length={result.2.length}, optimum={optimum}, " ++
    s!"left-subsequence={greedySubsequence left result.2}, " ++
    s!"right-subsequence={greedySubsequence right result.2}"

private def observe (label : String) (left right : List Nat) (result : Nat × List Nat)
    (optimum : Nat) : IO Unit := do
  let checks := inspect left right result optimum
  unless checks.all (fun check => check) do
    throw <| IO.userError <| s!"witness mismatch: {label}, checks={checks}, " ++
      details left right result optimum
  IO.println s!"PASS {label}: {details left right result optimum}"
  IO.println s!"CHECKS {label}: {checks}"

private def rejectResult (label : String) (left right : List Nat) (wrong : Nat × List Nat)
    (optimum : Nat) (expectedChecks : List Bool) : IO Unit := do
  observe s!"baseline {label}" left right (longestCommonSubsequence left right).ret optimum
  let checks := inspect left right wrong optimum
  unless checks == expectedChecks && !checks.all (fun check => check) do
    throw <| IO.userError s!"wrong result control failed: {label}, checks={checks}"
  IO.println s!"REJECT {label}: {details left right wrong optimum}"
  IO.println s!"CHECKS {label}: {checks}"

private def words : List (List Nat) :=
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1],
    [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1],
    [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1]]

private def runTests : IO Unit := do
  unless words.length == 15 && decide words.Nodup &&
      words.all (fun word => decide (word.length ≤ 3) && word.all (fun x => x == 0 || x == 1)) do
    throw <| IO.userError "binary word corpus mismatch"
  let mut pairs := 0
  let mut enumerated := 0
  for left in words do
    for right in words do
      let leftSequences := positionalSubsequences left
      let rightSequences := positionalSubsequences right
      unless leftSequences.length == 2 ^ left.length &&
          rightSequences.length == 2 ^ right.length do
        throw <| IO.userError "positional subsequence count mismatch"
      observe s!"pair {pairs}" left right (longestCommonSubsequence left right).ret
        (exhaustiveOptimum left right)
      enumerated := enumerated + leftSequences.length + rightSequences.length
      pairs := pairs + 1
  unless pairs == 225 do throw <| IO.userError "pair count mismatch"
  IO.println s!"PAIRS passed={pairs}, words=15, max-length=3, positional-entries={enumerated}"

  observe "anchor empty" [] [] (longestCommonSubsequence ([] : List Nat) []).ret 0
  observe "anchor empty left" [] [0, 1] (longestCommonSubsequence [] [0, 1]).ret 0
  observe "anchor empty right" [0, 1] [] (longestCommonSubsequence [0, 1] []).ret 0
  observe "anchor singleton" [0] [0] (longestCommonSubsequence [0] [0]).ret 1
  observe "anchor disjoint" [0, 0] [1, 1] (longestCommonSubsequence [0, 0] [1, 1]).ret 0
  observe "anchor repeated" [0, 0, 0] [0, 0] (longestCommonSubsequence [0, 0, 0] [0, 0]).ret 2
  observe "anchor identity" [0, 1, 0] [0, 1, 0] (longestCommonSubsequence [0, 1, 0] [0, 1, 0]).ret 3
  observe "anchor crossed" [0, 1] [1, 0] (longestCommonSubsequence [0, 1] [1, 0]).ret 1
  IO.println "ANCHORS passed=8 (extra observations)"

  let first : Nat × List Nat := (1, [0])
  let second : Nat × List Nat := (1, [1])
  observe "alternate zero" [0, 1] [1, 0] first 1
  observe "alternate one" [0, 1] [1, 0] second 1
  unless first.2 != second.2 do throw <| IO.userError "alternate witnesses were identical"
  IO.println "ALTERNATIVES passed=2, supplied-witnesses-differ=true"

  rejectResult "reversed order" [0, 1] [0, 1] (2, [1, 0])
    2 [false, false, true, true]
  rejectResult "extra left occurrence" [0, 1] [0, 0, 1] (2, [0, 0])
    2 [false, true, true, true]
  rejectResult "extra right occurrence" [0, 0, 1] [0, 1] (2, [0, 0])
    2 [true, false, true, true]
  let singleton := (longestCommonSubsequence [0] [0]).ret
  rejectResult "wrong reported length" [0] [0] (singleton.1 + 1, singleton.2)
    1 [true, true, false, false]
  rejectResult "valid nonoptimal witness" [0, 1] [0, 1] (1, [0])
    2 [true, true, true, false]
  IO.println "CONTROLS rejected=5, real-same-input-baselines=5"

#eval runTests

end Cslib.Algorithms.Lean.LongestCommonSubsequenceRuntimeTests
