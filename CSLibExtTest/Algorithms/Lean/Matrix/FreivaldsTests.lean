/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Freivalds
public meta import CSLibExt.Algorithms.Lean.Matrix.Freivalds
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Data.ZMod.Basic

/-!
# Freivalds execution tests

The noncommuting two-by-two factors exercise every binary seed and every
two-trial history. Incorrect products include both kernel acceptance and
rejection; all rejected histories still execute and charge every trial.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.Matrix

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.Matrix

private meta def verify (label : String) (actual : TimeM (Nat × Nat) Bool)
    (expected : Bool) (cost : Nat × Nat) : IO Unit := do
  unless actual.ret == expected do
    throw <| IO.userError s!"{label}: returned {actual.ret}, expected {expected}"
  unless actual.time == cost do
    throw <| IO.userError s!"{label}: scalar counts {actual.time}, expected {cost}"

private meta def runTests : IO Unit := do
  let one : Vector (Vector (ZMod 2) 1) 1 := #v[#v[1]]
  let zero : Vector (Vector (ZMod 2) 1) 1 := #v[#v[0]]
  verify "singleton correct" (freivaldsTrial one one one (fun _ => 1)) true (3, 3)
  verify "singleton kernel" (freivaldsTrial one one zero (fun _ => 0)) true (3, 3)
  verify "singleton rejection" (freivaldsTrial one one zero (fun _ => 1)) false (3, 3)
  IO.println "singleton: correct, kernel acceptance and rejection checked; counts (3, 3)"

  let A : Vector (Vector (ZMod 2) 2) 2 := #v[#v[1, 1], #v[0, 1]]
  let B : Vector (Vector (ZMod 2) 2) 2 := #v[#v[1, 0], #v[1, 1]]
  let C : Vector (Vector (ZMod 2) 2) 2 := #v[#v[0, 1], #v[1, 1]]
  let wrongC : Vector (Vector (ZMod 2) 2) 2 := #v[#v[1, 1], #v[1, 1]]
  let seeds : Array (Vector (ZMod 2) 2) := #[#v[0, 0], #v[0, 1], #v[1, 0], #v[1, 1]]
  let mut correctAccepted := 0
  let mut wrongAccepted := 0
  let mut seedIndex := 0
  for seed in seeds do
    let correct := freivaldsTrial A B C seed.get
    let wrong := freivaldsTrial A B wrongC seed.get
    verify s!"2x2 correct seed {seedIndex}" correct true (12, 12)
    verify s!"2x2 incorrect seed {seedIndex}" wrong (seed.get 0 == 0) (12, 12)
    if correct.ret then correctAccepted := correctAccepted + 1
    if wrong.ret then wrongAccepted := wrongAccepted + 1
    seedIndex := seedIndex + 1
  unless seedIndex == 4 && correctAccepted == 4 && wrongAccepted == 2 do
    throw <| IO.userError "2x2 complete seed counts differ"
  IO.println s!"2x2 trial: correct accepted {correctAccepted}/4, incorrect accepted {wrongAccepted}/4; counts (12, 12)"

  let mut correctHistories := 0
  let mut wrongHistories := 0
  let mut historyIndex := 0
  for left in seeds do
    for right in seeds do
      let history : Fin 2 → Fin 2 → ZMod 2 := fun i =>
        if i == 0 then left.get else right.get
      let correct := freivaldsRepeat A B C history
      let wrong := freivaldsRepeat A B wrongC history
      verify s!"2x2 correct history {historyIndex}" correct true (24, 24)
      verify s!"2x2 incorrect history {historyIndex}" wrong
        ((left.get 0 == 0) && (right.get 0 == 0)) (24, 24)
      if correct.ret then correctHistories := correctHistories + 1
      if wrong.ret then wrongHistories := wrongHistories + 1
      historyIndex := historyIndex + 1
  unless historyIndex == 16 && correctHistories == 16 && wrongHistories == 4 do
    throw <| IO.userError "2x2 complete history counts differ"
  IO.println s!"2x2 repeat: correct accepted {correctHistories}/16, incorrect accepted {wrongHistories}/16; counts (24, 24) even after rejection"

  let empty : Vector (Vector (ZMod 2) 0) 0 := #v[]
  verify "empty trial" (freivaldsTrial empty empty empty (fun i => Fin.elim0 i))
    true (0, 0)
  verify "empty two-trial history"
    (freivaldsRepeat empty empty empty (fun (_ : Fin 2) i => Fin.elim0 i)) true (0, 0)
  verify "zero trials, incorrect product"
    (freivaldsRepeat A B wrongC (fun (i : Fin 0) => Fin.elim0 i)) true (0, 0)
  IO.println "boundary: empty trial, empty repeated trial and zero trials checked; counts (0, 0)"

#eval runTests

end CSLibExtTest.Algorithms.Matrix
