/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.BinaryCounter
public meta import Cslib.Algorithms.Lean.TimeM

/-!
# Binary-counter actual execution fixtures

Thirty-two populated fixtures use only the ordinary public executors. The per-bit
and changed-bit diagnostics are canonical list expressions over actual returned
states, not another execution or a predicted cost. All eight deliberate wrong-
expectation branches remain available to an imported manual runner.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean.BinaryCounter

namespace Cslib.Algorithms.Lean.BinaryCounter.Tests

@[expose] public meta section

def checkCounts (label : String) (k n : Nat) (expected : List Nat) : IO Unit := do
  let counts := (List.range k).map fun i => ((List.range n).map fun t =>
    if (run (Vector.replicate k false) t).ret.toList.getD i false ≠
        (run (Vector.replicate k false) (t + 1)).ret.toList.getD i false
      then 1 else 0).sum
  let actual := run (Vector.replicate k false) n
  unless counts == expected && counts.sum == actual.time do
    throw <| IO.userError s!"{label}: actual flips={counts}, time={actual.time}; expected={expected}"
  IO.println s!"checked {label}: flips={counts}, time={actual.time}"

def checkAllCounts (args : List String) : IO Unit := do
  checkCounts "figure16.2-per-bit" 8 16
    (if args == ["flip"] then [15, 8, 4, 2, 1, 0, 0, 0] else [16, 8, 4, 2, 1, 0, 0, 0])
  checkCounts "zero-width-flips" 0 100 []
  checkCounts "zero-steps-flips" 5 0 [0, 0, 0, 0, 0]
  checkCounts "one-bit-repeated-wraps-flips" 1 5 [5]
  checkCounts "three-bit-full-wrap-flips" 3 8 [8, 4, 2]
  checkCounts "three-bit-repeated-wraps-flips" 3 17 [17, 8, 4]
  checkCounts "four-bit-repeated-wraps-flips" 4 33 [33, 16, 8, 4]
  checkCounts "eight-bit-full-wrap-flips" 8 256 [256, 128, 64, 32, 16, 8, 4, 2]

def checkRun {k : Nat} (label : String) (input : Vector Bool k) (n : Nat)
    (expectedBits : List Bool) (expectedTime expectedValue : Nat) : IO Unit := do
  let actual := run input n
  let value := (BitVec.ofBoolListLE actual.ret.toList).toNat
  unless actual.ret.toList == expectedBits && actual.ret.toList.length == k &&
      actual.time == expectedTime && value == expectedValue do
    throw <| IO.userError <|
      s!"{label}: got {actual.ret.toList}, time={actual.time}, value={value}; " ++
      s!"expected {expectedBits}, time={expectedTime}, value={expectedValue}"
  IO.println s!"checked {label}: {actual.ret.toList}, time={actual.time}, value={value}"

def checkAllRuns (args : List String) : IO Unit := do
  checkRun "source-figure16.2" (Vector.replicate 8 false) 16
    (if args == ["direction"] then [false, false, false, true, false, false, false, false]
      else [false, false, false, false, true, false, false, false])
    (if args == ["cost"] then 32 else 31) (if args == ["value"] then 17 else 16)
  checkRun "zero-width-100" (Vector.replicate 0 false) 100 [] 0 0
  checkRun "zero-steps-nonzero" (⟨#[true, false, true], by decide⟩ : Vector Bool 3)
    0 [true, false, true] 0 5
  checkRun "nonzero-carry-five-steps" (⟨#[true, false, true], by decide⟩ : Vector Bool 3)
    5 [false, true, false] 9 2
  checkRun "single-bit-five-steps" (Vector.replicate 1 false) 5 [true] 5 1
  checkRun "three-bit-full-wrap" (Vector.replicate 3 false) 8
    (if args == ["wrap"] then [false, false, false, true] else [false, false, false]) 14 0
  checkRun "three-bit-two-wraps-plus-one" (Vector.replicate 3 false) 17 [true, false, false] 29 1
  checkRun "four-bit-two-wraps-plus-one" (Vector.replicate 4 false) 33
    [true, false, false, false] 61 1
  checkRun "initial-overflow" (Vector.replicate 3 true) 1 [false, false, false] 3 0
  checkRun "high-suffix-unchanged" (⟨#[false, false, true], by decide⟩ : Vector Bool 3)
    2 [false, true, true] 3 6
  checkRun "zero-start-zero-steps" (Vector.replicate 5 false) 0
    [false, false, false, false, false] 0 0
  checkRun "eight-bit-full-wrap" (Vector.replicate 8 false) 256 (List.replicate 8 false) 510 0

def checkChanges {k : Nat} (label : String) (input : Vector Bool k)
    (expected : Nat) : IO Unit := do
  let actual := increment input
  let differences :=
    (List.zipWith (fun a b => if a ≠ b then 1 else 0) input.toList actual.ret.toList).sum
  unless actual.time == expected && differences == expected do
    throw <| IO.userError s!"{label}: time={actual.time}, changes={differences}; expected={expected}"
  IO.println s!"checked {label}: time={actual.time}, changes={differences}"

def checkBounds (label : String) (k n expected : Nat) : IO Unit := do
  let actual := run (Vector.replicate k false) n
  let total := ((List.range k).map fun i => n / 2 ^ i).sum
  unless actual.time == expected && actual.time == total &&
      (n == 0 || actual.time < 2 * n) && (k == 0 || n ≤ actual.time) do
    throw <| IO.userError s!"{label}: time={actual.time}, sum={total}; expected={expected}"
  IO.println s!"checked {label}: time={actual.time}, sum={total}, n={n}, k={k}"

def main (args : List String) : IO Unit := do
  checkAllCounts args
  checkAllRuns args
  checkChanges "zero-width-changes" (Vector.replicate 0 false) 0
  checkChanges "first-bit-change" (Vector.replicate 8 false) 1
  checkChanges "carry-three-changes" (⟨#[true, true, false, true], by decide⟩ : Vector Bool 4) 3
  checkChanges "full-overflow-changes" (Vector.replicate 3 true)
    (if args == ["changes"] then 4 else 3)
  checkBounds "figure16.2-sum-bound" 8 16 31
  checkBounds "zero-width-sum-bound" 0 100 0
  checkBounds "zero-steps-sum-bound" 5 0 0
  checkBounds "one-bit-sum-bound" 1 5 5
  checkBounds "full-wrap-sum-bound" 3 8 14
  checkBounds "repeated-wrap-sum-bound" 3 17 29
  checkBounds "wide-repeated-wrap-sum-bound" 4 33 61
  checkBounds "eight-bit-wrap-sum-bound" 8 256 510
  if args == ["upper"] then
    unless (run (Vector.replicate 8 false) 16).time < 31 do
      throw <| IO.userError "claimed upper bound time<31 is false: actual time=31"
  if args == ["lower"] then
    unless 30 ≤ (run (Vector.replicate 3 false) 17).time do
      throw <| IO.userError "claimed lower bound time>=30 is false: actual time=29"

#eval main []

end

end Cslib.Algorithms.Lean.BinaryCounter.Tests
