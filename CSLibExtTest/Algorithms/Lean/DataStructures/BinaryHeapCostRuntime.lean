/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.Cost
public import Mathlib.Data.Int.Order.Basic

public meta import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.Cost
public meta import Mathlib.Data.Int.Order.Basic

/-!
# Asserting sift-up runtime clients

All thirteen rows assert the returned array and both event counts before printing.
The assertions check selected events, not physical execution cost.
-/

public meta section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BinaryHeapCostRuntime

open Cslib.Algorithms.Lean

private def checkCase (label : String) (a : Array Int) (i : Nat)
    (expected : Array Int) (events : Nat × Nat) : IO Unit := do
  let result := TimeM.siftUp a i
  unless result.ret == expected && result.time == events do
    throw (IO.userError s!"{label}: wrong returned array or event counts")
  IO.println s!"{label}: comparisons={events.1} swaps={events.2}"

private def fullHeightInput : Array Int :=
  ((List.range 127).map fun n => (n : Int)).toArray.push (-1)

private def fullHeightExpected : Array Int :=
  (((List.range 127).map fun n => (n : Int)).toArray.push 63)
    |>.setIfInBounds 0 (-1) |>.setIfInBounds 1 0 |>.setIfInBounds 3 1
    |>.setIfInBounds 7 3 |>.setIfInBounds 15 7
    |>.setIfInBounds 31 15 |>.setIfInBounds 63 31

def main : IO Unit := do
  checkCase "empty" #[] 0 #[] (0, 0)
  checkCase "root" #[4] 0 #[4] (0, 0)
  checkCase "invalid" #[4] 1 #[4] (0, 0)
  checkCase "no-swap-depth1" #[1, 2] 1 #[1, 2] (1, 0)
  checkCase "swap-depth1" #[2, 1] 1 #[1, 2] (1, 1)
  checkCase "no-swap-depth2" #[1, 4, 2, 7] 3 #[1, 4, 2, 7] (1, 0)
  checkCase "full-height2" #[1, 4, 2, 7, 8, 9, 0] 6 #[0, 4, 1, 7, 8, 9, 2] (2, 2)
  checkCase "early-stop-depth2" #[1, 4, 3, 2] 3 #[1, 2, 3, 4] (2, 1)
  checkCase "early-stop-depth3" #[1, 4, 3, 6, 5, 7, 8, 2] 7 #[1, 2, 3, 4, 5, 7, 8, 6] (3, 2)
  checkCase "duplicates" #[1, 1, 1, 1] 3 #[1, 1, 1, 1] (1, 0)
  checkCase "negative" #[0, 4, 1, 7, 8, 9, -1] 6 #[-1, 4, 0, 7, 8, 9, 1] (2, 2)
  checkCase "off-path-violation" #[1, 9, 2, 0, 8, 9, 0] 6 #[0, 9, 1, 0, 8, 9, 2] (2, 2)
  checkCase "full-height7" fullHeightInput 127 fullHeightExpected (7, 7)

#eval main

end Cslib.Algorithms.Lean.BinaryHeapCostRuntime
