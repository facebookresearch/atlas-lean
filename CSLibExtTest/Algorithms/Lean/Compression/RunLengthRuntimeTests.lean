/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Compression.RunLength
public meta import CSLibExt.Algorithms.Lean.Compression.RunLength

/-!
# Exact run-length boundary execution tests

Five run lengths, both initial bits, and either end or an immediate opposite bit.
Literal chunk vectors specify packing independently of per-bit compression.
Existing documented, empty, 300-bit and alternating tests remain named anchors.
-/

namespace CSLibExtTest.Algorithms.Compression.RunLengthRuntime

open Cslib.Algorithms.Lean.RunLength

/-- Check exact packing, the count cap, and the observed expanded bits together. -/
private meta def accepts (bits : List Bool) (expected counts : List Nat)
    (expanded : List Bool) : Bool :=
  counts == expected && counts.all (fun n => decide (n ≤ 255)) && expanded == bits

/-- Observe both public operations and assert every part of the result check. -/
private meta def observe (label : String) (bits : List Bool) (expected : List Nat) :
    IO (List Nat) := do
  let counts := compress bits
  let expanded := expand counts
  unless accepts bits expected counts expanded do
    throw <| IO.userError s!"observation mismatch: {label}, counts={counts}, expected={expected}"
  IO.println s!"PASS {label}: input={bits.length}, counts={counts}, expanded={expanded.length}"
  return counts

/-- Reject a typed wrong observation only after its actual same-input baseline passes. -/
private meta def rejectObservation (label : String) (bits : List Bool) (expected : List Nat)
    (wrongCounts : List Nat) (wrongBits : List Bool) : IO Unit := do
  let _ ← observe ("baseline " ++ label) bits expected
  if accepts bits expected wrongCounts wrongBits then
    throw <| IO.userError s!"control accepted: {label}"
  let packed := wrongCounts == expected
  let capped := wrongCounts.all (fun n => decide (n ≤ 255))
  let sameBits := wrongBits == bits
  let sameLength := wrongBits.length == bits.length
  IO.println s!"REJECT {label}: counts={wrongCounts}, packed={packed}, cap={capped}"
  IO.println s!"  expanded-equal={sameBits}, expanded-length-equal={sameLength}"

/-- Run the twenty distinct shapes, old anchors, and three discriminating controls. -/
private meta def runTests : IO Unit := do
  let vectors : List (Nat × List Nat) :=
    [(254, [254]), (255, [255]), (256, [255, 0, 1]),
     (510, [255, 0, 255]), (511, [255, 0, 255, 0, 1])]
  let mut shapes := 0
  for (n, chunks) in vectors do
    for bit in [false, true] do
      for trailing in [false, true] do
        let bits := List.replicate n bit ++ (if trailing then [!bit] else [])
        let expected := (if bit then [0] else []) ++ chunks ++
          (if trailing then [1] else [])
        let _ ← observe s!"boundary {n} first={bit} transition={trailing}" bits expected
        shapes := shapes + 1
  unless shapes == 20 do
    throw <| IO.userError s!"boundary census mismatch: {shapes}"
  IO.println s!"BOUNDARIES passed={shapes}"

  let documented := List.replicate 15 false ++ List.replicate 7 true ++
    List.replicate 7 false ++ List.replicate 11 true
  let anchors : List (String × List Bool × List Nat) :=
    [("documented", documented, [15, 7, 7, 11]),
     ("empty", [], [0]),
     ("split-300", List.replicate 300 false, [255, 0, 45]),
     ("alternating", [true, false, true, false], [0, 1, 1, 1, 1])]
  let mut anchorCount := 0
  for (label, bits, expected) in anchors do
    let _ ← observe ("anchor " ++ label) bits expected
    anchorCount := anchorCount + 1
  unless anchorCount == 4 do
    throw <| IO.userError s!"anchor census mismatch: {anchorCount}"
  IO.println s!"ANCHORS passed={anchorCount}"

  let controls : List (String × List Bool × List Nat × List Nat × List Bool) :=
    [("tail-zeros", List.replicate 255 false, [255], [255, 0, 0], expand [255, 0, 0]),
     ("oversize-count", List.replicate 256 false, [255, 0, 1], [256], expand [256]),
     ("wrong-expansion", [true, false, true, false], [0, 1, 1, 1, 1],
       [0, 1, 1, 1, 1], List.replicate 4 false)]
  let mut controlCount := 0
  for (label, bits, expected, wrongCounts, wrongBits) in controls do
    rejectObservation label bits expected wrongCounts wrongBits
    controlCount := controlCount + 1
  unless controlCount == 3 do
    throw <| IO.userError s!"control census mismatch: {controlCount}"
  IO.println s!"CONTROLS rejected={controlCount}, baselines={controlCount}"

#eval runTests

end CSLibExtTest.Algorithms.Compression.RunLengthRuntime
