/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Bounds
public meta import CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Basic
public meta import Cslib.Algorithms.Lean.TimeM

namespace Cslib.Algorithms.Lean.Graph.HamiltonianCycleTests

private def check (label : String) (x y : Array Bool) (value : Bool) (time : Nat) : IO Unit := do
  let actual := Cslib.Algorithms.Lean.Graph.verifyHamiltonianCycle x y
  unless actual.ret == value && actual.time == time do
    throw (IO.userError s!"{label}: value={actual.ret} time={actual.time}, expected {value}/{time}")
  IO.println s!"U117_CASE {label} value={actual.ret} time={actual.time}"

private def runCases : IO Unit := do
  check "triangle"
    #[
      false, true, true, true, false, true, true, true, false]
    #[
      false, false, true, false, false, true]
    true 39
  check "missing-closing"
    #[
      false, true, false, true, false, true, false, true, false]
    #[
      false, false, true, false, false, true]
    false 39
  check "triangle-reverse"
    #[
      false, true, true, true, false, true, true, true, false]
    #[
      false, false, false, true, true, false]
    true 39
  check "square"
    #[
      false, true, false, true, true, false, true, false, false, true,
      false, true, true, false, true, false]
    #[
      false, false, true, false, false, true, true, true]
    true 57
  check "square-rotation"
    #[
      false, true, false, true, true, false, true, false, false, true,
      false, true, true, false, true, false]
    #[
      false, true, true, true, false, false, true, false]
    true 57
  check "square-repeated-local-walk"
    #[
      false, true, false, true, true, false, true, false, false, true,
      false, true, true, false, true, false]
    #[
      false, false, true, false, false, false, true, true]
    false 45
  check "square-nonedge"
    #[
      false, true, false, true, true, false, true, false, false, true,
      false, true, true, false, true, false]
    #[
      false, false, false, true, true, false, true, true]
    false 41
  check "out-of-range-last"
    #[
      false, true, true, true, false, true, true, true, false]
    #[
      false, false, true, false, true, true]
    false 33
  check "out-of-range-first"
    #[
      false, true, true, true, false, true, true, true, false]
    #[
      true, true, true, false, false, true]
    false 21
  check "duplicate-second"
    #[
      false, true, true, true, false, true, true, true, false]
    #[
      false, false, false, false, false, true]
    false 27
  check "missing-word"
    #[
      false, true, true, true, false, true, true, true, false]
    #[
      false, false, true, false]
    false 18
  check "extra-word"
    #[
      false, true, true, true, false, true, true, true, false]
    #[
      false, false, true, false, false, true, false, false]
    false 18
  check "partial-word"
    #[
      false, true, true, true, false, true, true, true, false]
    #[
      false, false, true, false, false]
    false 18
  check "extra-bit"
    #[
      false, true, true, true, false, true, true, true, false]
    #[
      false, false, true, false, false, true, false]
    false 18
  check "empty-certificate"
    #[
      false, true, true, true, false, true, true, true, false]
    #[]
    false 18
  check "nonsquare-graph"
    #[
      false, true, true, true, false, true, true, true]
    #[
      false, false, true, false, false, true]
    false 1
  check "asymmetric"
    #[
      false, true, true, false, false, true, true, true, false]
    #[
      false, false, true, false, false, true]
    false 10
  check "self-loop"
    #[
      true, true, true, true, false, true, true, true, false]
    #[
      false, false, true, false, false, true]
    false 3
  check "zero-vertices"
    #[]
    #[]
    false 2
  check "one-vertex"
    #[
      false]
    #[]
    false 4
  check "two-vertices"
    #[
      false, true, true, false]
    #[
      false, true]
    false 9
  check "one-loop"
    #[
      true]
    #[]
    false 3
  check "pentagon-little-endian"
    #[
      false, true, false, false, true, true, false, true, false, false,
      false, true, false, true, false, false, false, true, false, true,
      true, false, false, true, false]
    #[
      false, false, false, true, false, false, false, true, false, true,
      true, false, false, false, true]
    true 83
  check "pentagon-msb-words"
    #[
      false, true, false, false, true, true, false, true, false, false,
      false, true, false, true, false, false, false, true, false, true,
      true, false, false, true, false]
    #[
      false, false, false, false, false, true, false, true, false, false,
      true, true, true, false, false]
    false 65
  IO.println "U117_ACTUAL_CASES 24"

#eval runCases

end Cslib.Algorithms.Lean.Graph.HamiltonianCycleTests
