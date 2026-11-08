/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.ExactSubsetSum
public meta import Mathlib.Algebra.GroupWithZero.Nat

/-! Ordinary-import runtime fixtures for the actual saved-list executor.
The printed example, equality pruning, collisions, source order and Nat extensions
have independent source-transcribed expected lists and selected-event counts. -/

public meta section

open Cslib.Algorithms.Lean.ExactSubsetSum

namespace Cslib.Algorithms.Lean.ExactSubsetSum.Tests

private def verify (name : String) (xs : List Nat) (target : Nat)
    (prefixes : List (List Nat)) (value count : Nat) : IO Unit := do
  let actual := exactSubsetSum xs target
  let saved := (List.range (xs.length + 1)).map fun i =>
    (exactSubsetSumSums (xs.take i) target).ret
  unless saved == prefixes do
    throw (IO.userError s!"{name}: wrong prefixes, expected {prefixes}, actual {saved}")
  unless actual.ret == value do
    throw (IO.userError s!"{name}: wrong value, expected {value}, actual {actual.ret}")
  unless actual.time == count do
    throw (IO.userError s!"{name}: wrong time, expected {count}, actual {actual.time}")
  unless actual.time ≤ 1 + xs.length + 7 * (2 ^ xs.length - 1) + 2 ^ xs.length do
    throw (IO.userError s!"{name}: exponential upper bound violated")
  unless actual.time ≤ 1 + xs.length +
      (7 * xs.length + 1) * min (target + 1) (xs.sum + 1) do
    throw (IO.userError s!"{name}: numeric upper bound violated")
  IO.println s!"{name}: xs={xs}, target={target}, prefixes={saved}, ret={actual.ret}, time={actual.time}"

private def runAllCases : IO Unit := do
  verify "empty" [] 7 [[0]] 0 2
  verify "singleton-fit" [5] 5 [[0], [0, 5]] 5 9
  verify "singleton-pruned" [5] 4 [[0], [0]] 0 8
  verify "printed-P-example" [1, 4, 5] 10
    [[0], [0, 1], [0, 1, 4, 5], [0, 1, 4, 5, 6, 9, 10]] 10 49
  verify "printed-P-truncated" [1, 4, 5] 8
    [[0], [0, 1], [0, 1, 4, 5], [0, 1, 4, 5, 6]] 6 47
  verify "sum-collision-boundary" [1, 4, 5] 5
    [[0], [0, 1], [0, 1, 4, 5], [0, 1, 4, 5]] 5 46
  verify "input-order" [5, 1, 4] 8
    [[0], [0, 5], [0, 1, 5, 6], [0, 1, 4, 5, 6]] 6 50
  verify "all-too-heavy" [10, 11] 9 [[0], [0], [0]] 0 14
  verify "powers-two" [1, 2, 4, 8, 16] 31
    [[0], List.range 2, List.range 4, List.range 8, List.range 16, List.range 32] 31 219
  verify "multiple-collisions" [1, 2, 3, 4] 10
    [[0], [0, 1], [0, 1, 2, 3], List.range 7, List.range 11] 10 94
  verify "repeated-positions-extension" [5, 5] 10 [[0], [0, 5], [0, 5, 10]] 10 21
  verify "zero-items-extension" [0, 0, 2] 0 [[0], [0], [0], [0]] 0 18
  verify "zero-target-extension" [1, 2] 0 [[0], [0], [0]] 0 14

#eval runAllCases

end Cslib.Algorithms.Lean.ExactSubsetSum.Tests
