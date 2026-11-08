/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Matrix.Assignments
public meta import Cslib.Algorithms.Lean.TimeM

import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.SlowAPSP

/-!
# SLOW-APSP runtime fixtures

Complete source Figure23.1 tables and varied saved inputs execute the actual
public algorithm. Intermediate tables invoke the production phase closure.
Wrong expectations throw, and the full suite is restored in the ordinary build.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean

namespace U086RuntimeFixtures

private abbrev Raw := WithTop Int
private abbrev Scalar := MinTropical Raw
private abbrev Cost := Nat × (Nat × Nat)
private abbrev RawTable (n : Nat) := Vector (Vector Raw n) n
private abbrev Table (n : Nat) := Vector (Vector Scalar n) n

private def tropTable {n : Nat} (A : RawTable n) : Table n :=
  A.map fun row => row.map MinTropical.trop

private def untropTable {n : Nat} (A : Table n) : RawTable n :=
  A.map fun row => row.map MinTropical.untrop

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw <| IO.userError message

private def expectFailure (label : String) (action : IO Unit) : IO Unit := do
  let rejected ← try
    action
    pure false
  catch _ =>
    pure true
  ensure rejected s!"negative control did not fail: {label}"
  IO.println s!"negative-control.{label}=rejected"

private def render {n : Nat} (A : RawTable n) : String :=
  reprStr (A.toArray.map (·.toArray))

private def printResult {n : Nat} (name : String)
    (output : RawTable n) (cost : Cost) : IO Unit := do
  IO.println s!"{name}.ret={render output}"
  IO.println s!"{name}.writes={cost.1}"
  IO.println s!"{name}.additions={cost.2.1}"
  IO.println s!"{name}.minima={cost.2.2}"

private def verifyCase {n : Nat} (name : String) (W L0 expected : RawTable n)
    (expectedCost : Cost) : IO String := do
  let savedW := W
  let savedL0 := L0
  let actual := Matrix.slowAPSP (tropTable W) (tropTable L0)
  let output := untropTable actual.ret
  ensure (decide (output = expected)) s!"{name}: wrong output {render output}"
  ensure (decide (actual.time = expectedCost))
    s!"{name}: wrong cost {actual.time}"
  ensure (decide (W = savedW ∧ L0 = savedL0))
    s!"{name}: an input changed"
  printResult name output actual.time
  pure s!"{name}|{render output}|{actual.time}"

private def figureW : RawTable 5 :=
  #v[
    #v[0, 3, 8, ⊤, -4],
    #v[⊤, 0, ⊤, 1, 7],
    #v[⊤, 4, 0, ⊤, ⊤],
    #v[2, ⊤, -5, 0, ⊤],
    #v[⊤, ⊤, ⊤, 6, 0]]

private def identity5 : RawTable 5 :=
  #v[
    #v[0, ⊤, ⊤, ⊤, ⊤],
    #v[⊤, 0, ⊤, ⊤, ⊤],
    #v[⊤, ⊤, 0, ⊤, ⊤],
    #v[⊤, ⊤, ⊤, 0, ⊤],
    #v[⊤, ⊤, ⊤, ⊤, 0]]

private def figureL2 : RawTable 5 :=
  #v[
    #v[0, 3, 8, 2, -4],
    #v[3, 0, -4, 1, 7],
    #v[⊤, 4, 0, 5, 11],
    #v[2, -1, -5, 0, -2],
    #v[8, ⊤, 1, 6, 0]]

private def figureL3 : RawTable 5 :=
  #v[
    #v[0, 3, -3, 2, -4],
    #v[3, 0, -4, 1, -1],
    #v[7, 4, 0, 5, 11],
    #v[2, -1, -5, 0, -2],
    #v[8, 5, 1, 6, 0]]

private def figureL4 : RawTable 5 :=
  #v[
    #v[0, 1, -3, 2, -4],
    #v[3, 0, -4, 1, -1],
    #v[7, 4, 0, 5, 3],
    #v[2, -1, -5, 0, -2],
    #v[8, 5, 1, 6, 0]]

private def figureStages : List (RawTable 5) :=
  [identity5, figureW, figureL2, figureL3, figureL4]

/- Each diagnostic prefix invokes the production runPhases closure on the
actual production copyCells result. Prefixes are re-executed to observe their
tables; their diagnostic work is not counted as one slowAPSP execution. -/
private def productionStages {n : Nat} (W L0 : Table n) : List (Table n) :=
  List.ofFn fun r : Fin n =>
    (Matrix.runPhases W r.val (Matrix.copyCells L0).ret).ret

private def verifyFigureStages : IO Unit := do
  let actual := Matrix.slowAPSP (tropTable figureW) (tropTable identity5)
  let stages :=
    (productionStages (tropTable figureW) (tropTable identity5)).map untropTable
  ensure (decide (stages = figureStages)) "figure23.1: wrong saved stages"
  ensure (decide (stages.getLast? = some (untropTable actual.ret)))
    "figure23.1: production final stage differs from public execution"
  ensure (decide (actual.time = (225, (500, 500))))
    s!"figure23.1: wrong trace cost {actual.time}"
  ensure (decide (stages.length = 5)) "figure23.1: not four extensions"
  let mut phase := 0
  for stage in stages do
    IO.println s!"figure23.1.L{phase}={render stage}"
    phase := phase + 1
  IO.println s!"figure23.1.trace.writes={actual.time.1}"
  IO.println s!"figure23.1.trace.additions={actual.time.2.1}"
  IO.println s!"figure23.1.trace.minima={actual.time.2.2}"

private def identity2 : RawTable 2 :=
  #v[#v[0, ⊤], #v[⊤, 0]]

private def identity3 : RawTable 3 :=
  #v[#v[0, ⊤, ⊤], #v[⊤, 0, ⊤], #v[⊤, ⊤, 0]]

private def identity4 : RawTable 4 :=
  #v[
    #v[0, ⊤, ⊤, ⊤],
    #v[⊤, 0, ⊤, ⊤],
    #v[⊤, ⊤, 0, ⊤],
    #v[⊤, ⊤, ⊤, 0]]

private def disconnected2 : RawTable 2 := identity2

private def signedW : RawTable 3 :=
  #v[#v[0, -2, 9], #v[⊤, 0, 3], #v[⊤, ⊤, 0]]

private def signedExpected : RawTable 3 :=
  #v[#v[0, -2, 1], #v[⊤, 0, 3], #v[⊤, ⊤, 0]]

private def zeroTies : RawTable 3 :=
  #v[#v[0, 0, 0], #v[0, 0, 0], #v[0, 0, 0]]

private def chainW : RawTable 4 :=
  #v[
    #v[0, 2, ⊤, ⊤],
    #v[⊤, 0, 3, ⊤],
    #v[⊤, ⊤, 0, 4],
    #v[⊤, ⊤, ⊤, 0]]

private def chainExpected : RawTable 4 :=
  #v[
    #v[0, 2, 5, 9],
    #v[⊤, 0, 3, 7],
    #v[⊤, ⊤, 0, 4],
    #v[⊤, ⊤, ⊤, 0]]

private def chainWithoutLastPhase : RawTable 4 :=
  #v[
    #v[0, 2, 5, ⊤],
    #v[⊤, 0, 3, 7],
    #v[⊤, ⊤, 0, 4],
    #v[⊤, ⊤, ⊤, 0]]

private def negativeCycleW : RawTable 2 :=
  #v[#v[0, -1], #v[-1, 0]]

private def arbitraryW : RawTable 3 :=
  #v[#v[1, 2, 5], #v[4, 0, 3], #v[2, 6, -1]]

private def arbitraryL0 : RawTable 3 :=
  #v[#v[7, 4, 8], #v[2, 9, 3], #v[5, 1, 6]]

private def arbitraryExpected : RawTable 3 :=
  #v[#v[8, 4, 6], #v[4, 4, 1], #v[5, 1, 3]]

private def zeroResetWrong : RawTable 3 :=
  #v[#v[0, 2, 5], #v[4, 0, 1], #v[2, 1, -1]]

private def reversedWrong : RawTable 3 :=
  #v[#v[4, 5, 5], #v[2, 3, 3], #v[3, -1, 4]]

private def sameValues : RawTable 2 :=
  #v[#v[0, 4], #v[2, 0]]

private def negativeDiagonalW : RawTable 2 :=
  #v[#v[-2, ⊤], #v[⊤, 0]]

private def actualOutput {n : Nat} (W L0 : RawTable n) : RawTable n :=
  untropTable (Matrix.slowAPSP (tropTable W) (tropTable L0)).ret

private def verifyNegativeControls : IO Unit := do
  let figureActual := Matrix.slowAPSP (tropTable figureW) (tropTable identity5)
  let wrongFigure : RawTable 5 :=
    #v[
      #v[0, 999, -3, 2, -4],
      #v[3, 0, -4, 1, -1],
      #v[7, 4, 0, 5, 3],
      #v[2, -1, -5, 0, -2],
      #v[8, 5, 1, 6, 0]]
  expectFailure "wrong-output" do
    ensure (decide (untropTable figureActual.ret = wrongFigure))
      "wrong output detected"
  expectFailure "wrong-scalar-count" do
    ensure (decide (figureActual.time = (225, (499, 500))))
      "wrong scalar count detected"
  expectFailure "omitted-copy-charge" do
    ensure (decide (figureActual.time = (125, (500, 500))))
      "omitted copy charge detected"
  expectFailure "omitted-final-phase" do
    ensure (decide (actualOutput chainW identity4 = chainWithoutLastPhase))
      "omitted final phase detected"
  expectFailure "zero-reset" do
    ensure (decide (actualOutput arbitraryW arbitraryL0 = zeroResetWrong))
      "zero reset detected"
  expectFailure "reversed-operands" do
    ensure (decide (actualOutput arbitraryW arbitraryL0 = reversedWrong))
      "reversed operands detected"
  IO.println "negative-controls=6 rejected"

private def runSuite : IO (List String) := do
  let f1 ← verifyCase "figure23.1-all-stages" figureW identity5 figureL4
    (225, (500, 500))
  let f2 ← verifyCase "empty" (#v[] : RawTable 0) #v[] #v[] (0, (0, 0))
  let f3 ← verifyCase "singleton-source" #v[#v[0]] #v[#v[0]] #v[#v[0]]
    (1, (0, 0))
  let f4 ← verifyCase "singleton-saved-L0" #v[#v[8]] #v[#v[7]] #v[#v[7]]
    (1, (0, 0))
  let f5 ← verifyCase "two-disconnected" disconnected2 identity2 identity2
    (12, (8, 8))
  let f6 ← verifyCase "signed-acyclic" signedW identity3 signedExpected
    (45, (54, 54))
  let f7 ← verifyCase "tied-zero-cycles" zeroTies identity3 zeroTies
    (45, (54, 54))
  let f8 ← verifyCase "last-phase-chain" chainW identity4 chainExpected
    (112, (192, 192))
  let f9 ← verifyCase "negative-cycle-bounded-only" negativeCycleW identity2
    negativeCycleW (12, (8, 8))
  let f10 ← verifyCase "arbitrary-L0-noncommuting" arbitraryW arbitraryL0
    arbitraryExpected (45, (54, 54))
  let f11 ← verifyCase "same-object-input-values" sameValues sameValues sameValues
    (12, (8, 8))
  let f12 ← verifyCase "finite-negative-diagonal" negativeDiagonalW identity2
    negativeDiagonalW (12, (8, 8))
  pure [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12]

#eval do
  let baseline ← runSuite
  verifyFigureStages
  verifyNegativeControls
  let restored ← runSuite
  ensure (decide (restored = baseline)) "restored suite differs from baseline"
  IO.println "restoration=exact full suite"

end U086RuntimeFixtures
