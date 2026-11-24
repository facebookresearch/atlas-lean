/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Selection.Quickselect
meta import CSLibExt.Algorithms.Lean.Selection.Quickselect

namespace Cslib.Algorithms.Lean.TimeM.QuickselectRuntime

/-- Check an observation using only membership and counts in the original input. -/
private def observesRank (xs : List Nat) (rank : Nat) : Option Nat → Bool
  | none => decide (xs.length ≤ rank)
  | some x => decide (x ∈ xs) &&
      decide (xs.countP (fun y => decide (y < x)) ≤ rank) &&
      decide (rank < xs.countP (fun y => decide (y ≤ x)))

/-- Enumerate lists of one fixed length over the three-element alphabet. -/
private def listsOfLength : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => [0, 1, 2].flatMap fun x => (listsOfLength n).map (x :: ·)

/-- All ternary lists through length four; ranks are enumerated separately. -/
private def corpus : List (List Nat) := (List.range 5).flatMap listsOfLength

/-- Literal rank anchors, including duplicates and the three root input classes. -/
private def anchors : List (String × List Nat × Nat × Option Nat) :=
  [("empty", [], 0, none),
   ("singleton", [7], 0, some 7),
   ("singleton-none", [7], 2, none),
   ("root-below", [1, 0, 2], 0, some 0),
   ("root-equal-start", [1, 0, 1, 2], 1, some 1),
   ("root-equal-end", [1, 0, 1, 2], 2, some 1),
   ("root-above", [1, 0, 1, 2], 3, some 2),
   ("boundary-none", [1, 0, 1, 2], 4, none),
   ("ascending", [0, 1, 2], 1, some 1),
   ("descending", [2, 1, 0], 1, some 1),
   ("all-equal-start", [5, 5, 5], 0, some 5),
   ("all-equal-end", [5, 5, 5], 2, some 5)]

/-- Reject a bad observation and retain its input in the failure message. -/
private def checkObservation (xs : List Nat) (rank : Nat) (actual : Option Nat) : IO Unit := do
  unless observesRank xs rank actual do
    throw <| IO.userError s!"rank mismatch: xs={xs}, rank={rank}, actual={actual}"

/-- Check both the count predicate and the independently specified literal anchors. -/
private def checkAnchors : IO Unit := do
  for (name, xs, rank, expected) in anchors do
    let actual := (quickselect xs rank).ret
    checkObservation xs rank actual
    unless actual == expected do
      throw <| IO.userError
        s!"anchor mismatch: {name}, xs={xs}, rank={rank}, actual={actual}, expected={expected}"
    IO.println s!"ANCHOR {name}: xs={xs}, rank={rank}, actual={actual}"
  IO.println s!"ANCHORS passed={anchors.length}"

/-- Three distinct typed wrong observations, each with a passing same-input baseline. -/
private def checkControls : IO Unit := do
  let controls : List (String × List Nat × Nat × Option Nat) :=
    [("adjacent-rank", [0, 1], 0, some 1),
     ("false-absence", [0, 1], 0, none),
     ("false-presence", [0, 1], 2, some 0)]
  for (name, xs, rank, wrong) in controls do
    let baseline := (quickselect xs rank).ret
    checkObservation xs rank baseline
    if observesRank xs rank wrong then
      throw <| IO.userError s!"control accepted: {name}, xs={xs}, rank={rank}, wrong={wrong}"
    IO.println s!"REJECT {name}: xs={xs}, rank={rank}, baseline={baseline}, wrong={wrong}"
  IO.println s!"CONTROLS rejected={controls.length}, baselines={controls.length}"

/-- Check every generated call; classify root inputs without instrumenting the algorithm. -/
private def checkCorpus : IO Unit := do
  unless corpus.length == 121 && corpus.eraseDups.length == 121 do
    throw <| IO.userError s!"list census mismatch: lists={corpus.length}"
  let mut calls := 0
  let mut successes := 0
  let mut absent := 0
  let mut below := 0
  let mut equalBlock := 0
  let mut above := 0
  for xs in corpus do
    for rank in List.range (xs.length + 2) do
      let actual := (quickselect xs rank).ret
      checkObservation xs rank actual
      calls := calls + 1
      if actual.isSome then successes := successes + 1 else absent := absent + 1
      if rank < xs.length then
        if let pivot :: _ := xs then
          if rank < xs.countP (fun y => decide (y < pivot)) then
            below := below + 1
          else if rank < xs.countP (fun y => decide (y ≤ pivot)) then
            equalBlock := equalBlock + 1
          else
            above := above + 1
  unless (calls, successes, absent, below, equalBlock, above) == (668, 426, 242, 102, 222, 102) do
    throw <| IO.userError
      (s!"call census mismatch: calls={calls}, some={successes}, none={absent}, " ++
        s!"below={below}, equal={equalBlock}, above={above}")
  IO.println s!"CORPUS lists={corpus.length}, calls={calls}, some={successes}, none={absent}"
  IO.println s!"ROOT INPUTS below={below}, equal-block={equalBlock}, above={above}"

/-- Exercise the public return values through one ordinary asserting evaluation. -/
private def runTests : IO Unit := do
  checkAnchors
  checkControls
  checkCorpus

#eval runTests

end Cslib.Algorithms.Lean.TimeM.QuickselectRuntime
