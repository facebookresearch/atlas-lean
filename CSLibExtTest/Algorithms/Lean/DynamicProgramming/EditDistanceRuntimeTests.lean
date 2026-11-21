/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Algorithm
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Script

/-!
# Runtime tests for returned edit scripts

All binary list pairs through length three check returned scripts with public application,
an indexed source-cursor replay, an independent edit count, and exhaustive alignment-path
costs. Literal anchors, different tied optima and wrong legal records check the observer.
The edit-cost recurrence is shared mathematics; this is finite executable coverage.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.EditDistanceRuntimeTests

-- Expand every monotone alignment path without merging equal states or equal costs.
private def pathCosts (source target : List Nat) : List Nat :=
  let initial : List (List Nat × List Nat × Nat) := [(source, target, 0)]
  let paths := (List.range (source.length + target.length)).foldl (fun frontier _ =>
    frontier.flatMap (fun (remainingSource, remainingTarget, cost) =>
      match remainingSource, remainingTarget with
      | [], [] => [([], [], cost)]
      | _ :: rest, [] => [(rest, [], cost + 1)]
      | [], _ :: rest => [([], rest, cost + 1)]
      | x :: restSource, y :: restTarget =>
          [(restSource, y :: restTarget, cost + 1),
            (x :: restSource, restTarget, cost + 1),
            (restSource, restTarget, cost + if x == y then 0 else 1)])) initial
  paths.map (fun (_, _, cost) => cost)

private def exhaustiveOptimum (source target : List Nat) : Nat :=
  (pathCosts source target).foldl min (source.length + target.length)

-- Replay by a source cursor; every consuming step must match its stored payload.
private def cursorApply? (source : List Nat) (script : EditScript Nat) :
    Option (List Nat) := do
  let input := source.toArray
  let mut cursor := 0
  let mut output : Array Nat := #[]
  for step in script do
    match step with
    | .keep value =>
        let consumed ← input[cursor]?
        if consumed != value then none else pure ()
        cursor := cursor + 1
        output := output.push value
    | .delete value =>
        let consumed ← input[cursor]?
        if consumed != value then none else pure ()
        cursor := cursor + 1
    | .insert value => output := output.push value
    | .substitute value replacement =>
        let consumed ← input[cursor]?
        if consumed != value then none else pure ()
        cursor := cursor + 1
        output := output.push replacement
  if cursor == input.size then return output.toList else none

private def editCount (script : EditScript Nat) : Nat :=
  script.foldl (fun count step => match step with
    | .keep _ => count
    | .delete _ | .insert _ | .substitute _ _ => count + 1) 0

-- Codes 0/1/2/3 mean keep/delete/insert/substitute; other fields are source/target payloads.
private def scriptData (script : EditScript Nat) : List (Nat × Nat × Nat) :=
  script.map (fun step => match step with
    | .keep value => (0, value, value)
    | .delete value => (1, value, 0)
    | .insert value => (2, 0, value)
    | .substitute source target => (3, source, target))

-- Evaluate every conjunct separately, including when an application observer rejects.
private def inspect (source target : List Nat) (result : EditDistanceResult Nat)
    (optimum : Nat) : List Bool :=
  [result.script.apply? source == some target,
    cursorApply? source result.script == some target,
    result.script.cost == editCount result.script,
    result.distance == editCount result.script,
    result.distance == optimum]

private def details (source target : List Nat) (result : EditDistanceResult Nat)
    (optimum : Nat) : String :=
  s!"source={source}, target={target}, distance={result.distance}, optimum={optimum}, " ++
    s!"steps={scriptData result.script}, public-apply={result.script.apply? source}, " ++
    s!"cursor-apply={cursorApply? source result.script}, " ++
    s!"public-cost={result.script.cost}, counted-cost={editCount result.script}"

private def observe (label : String) (source target : List Nat)
    (result : EditDistanceResult Nat) (optimum : Nat) : IO (List Nat) := do
  let checks := inspect source target result optimum
  unless checks.all (fun check => check) do
    throw <| IO.userError <| s!"result mismatch: {label}, checks={checks}, " ++
      details source target result optimum
  IO.println s!"PASS {label}: {details source target result optimum}"
  IO.println s!"CHECKS {label}: {checks}"
  return (scriptData result.script).map Prod.fst

private def rejectResult (label : String) (source target : List Nat)
    (wrong : EditDistanceResult Nat) (optimum : Nat) (expectedChecks : List Bool) :
    IO Unit := do
  let _ ← observe s!"baseline {label}" source target (editDistance source target).ret optimum
  let checks := inspect source target wrong optimum
  unless checks == expectedChecks && !checks.all (fun check => check) do
    throw <| IO.userError s!"wrong result control failed: {label}, checks={checks}"
  IO.println s!"REJECT {label}: {details source target wrong optimum}"
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
  let mut paths := 0
  let mut constructors : List Nat := []
  for source in words do
    for target in words do
      let costs := pathCosts source target
      unless !costs.isEmpty do
        throw <| IO.userError "alignment path enumeration was empty"
      let observed ← observe s!"pair {pairs}" source target
        (editDistance source target).ret (exhaustiveOptimum source target)
      constructors := observed ++ constructors
      paths := paths + costs.length
      pairs := pairs + 1
  unless pairs == 225 do
    throw <| IO.userError "pair count mismatch"
  IO.println s!"PAIRS passed={pairs}, words=15, max-length=3, alignment-paths={paths}"
  unless [0, 1, 2, 3].all (fun code => constructors.contains code) do
    throw <| IO.userError "actual scripts did not cover all step constructors"
  IO.println "CONSTRUCTORS observed=4, codes=0/1/2/3 (keep/delete/insert/substitute)"

  let _ ← observe "anchor empty" [] [] (editDistance ([] : List Nat) []).ret 0
  let _ ← observe "anchor insert" [] [0, 1] (editDistance [] [0, 1]).ret 2
  let _ ← observe "anchor delete" [0, 1] [] (editDistance [0, 1] []).ret 2
  let _ ← observe "anchor identity" [0, 1] [0, 1] (editDistance [0, 1] [0, 1]).ret 0
  let _ ← observe "anchor substitution" [0] [1] (editDistance [0] [1]).ret 1
  let _ ← observe "anchor drop head" [0, 1] [1] (editDistance [0, 1] [1]).ret 1
  let _ ← observe "anchor append" [0] [0, 1] (editDistance [0] [0, 1]).ret 1
  let _ ← observe "anchor swap" [0, 1] [1, 0] (editDistance [0, 1] [1, 0]).ret 2
  IO.println "ANCHORS passed=8 (extra observations)"

  let first : EditDistanceResult Nat := ⟨2, [.substitute 0 1, .substitute 1 0]⟩
  let second : EditDistanceResult Nat := ⟨2, [.delete 0, .keep 1, .insert 0]⟩
  let _ ← observe "alternate substitutions" [0, 1] [1, 0] first 2
  let _ ← observe "alternate delete keep insert" [0, 1] [1, 0] second 2
  unless first.script != second.script do
    throw <| IO.userError "alternate optimum fixture was identical"
  IO.println "ALTERNATIVES passed=2, actual-supplied-scripts-differ=true"

  let substituted := (editDistance [0] [1]).ret
  let identityResult := (editDistance [0, 1] [0, 1]).ret
  rejectResult "wrong consumed payload" [0] [1]
    { substituted with script := [.substitute 9 1] } 1 [false, false, true, true, true]
  rejectResult "leftover source" [0, 1] [0, 1]
    { identityResult with script := identityResult.script.take 1 }
    0 [false, false, true, true, true]
  rejectResult "wrong distance" [0] [1]
    { substituted with distance := substituted.distance + 1 }
    1 [true, true, true, false, false]
  rejectResult "valid nonoptimal script" [0] [1]
    ⟨2, [.delete 0, .insert 1]⟩ 1 [true, true, true, true, false]
  IO.println "CONTROLS rejected=4, real-same-input-baselines=4"

#eval runTests

end Cslib.Algorithms.Lean.EditDistanceRuntimeTests
