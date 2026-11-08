/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.SiftDownCost
public import Mathlib.Data.Int.Order.Basic

public meta import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.SiftDownCost
public meta import Mathlib.Data.Int.Order.Basic

/-! # Asserting sift-down event clients -/

public meta section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SiftDownCostRuntime

open Cslib.Algorithms.Lean

private def checkCase (label : String) (a : Array Int) (i : Nat)
    (expected : Array Int) (events : Nat × Nat) : IO Unit := do
  let result := TimeM.siftDown a i
  unless result.ret == expected && result.time == events do
    throw (IO.userError s!"{label}: wrong returned array or event counts")
  IO.println s!"{label}: comparisons={events.1} swaps={events.2}"

def main : IO Unit := do
  checkCase "empty" #[] 0 #[] (0, 0)
  checkCase "singleton" #[7] 0 #[7] (0, 0)
  checkCase "invalid" #[7] 1 #[7] (0, 0)
  checkCase "one-child" #[2, 1] 0 #[1, 2] (1, 1)
  checkCase "left-smaller" #[3, 1, 2] 0 #[1, 3, 2] (2, 1)
  checkCase "no-swap" #[0, 1, 2] 0 #[0, 1, 2] (2, 0)
  checkCase "equal-parent" #[1, 1, 2] 0 #[1, 1, 2] (2, 0)
  checkCase "left-tie" #[5, 1, 1] 0 #[1, 5, 1] (2, 1)
  checkCase "right-smaller" #[5, 2, 1] 0 #[1, 2, 5] (2, 1)
  checkCase "negative" #[0, -2, -1] 0 #[-2, 0, -1] (2, 1)
  checkCase "full-height2" #[10, 2, 3, 4, 5, 6, 7] 0 #[2, 4, 3, 10, 5, 6, 7] (4, 2)
  checkCase "early-stop" #[5, 1, 6, 9, 10, 7, 8] 0 #[1, 5, 6, 9, 10, 7, 8] (4, 1)
  checkCase "off-path-violation" #[10, 2, 3, 4, 1, 6, 7] 0 #[2, 1, 3, 4, 10, 6, 7] (4, 2)
  checkCase "right-spine" #[10, 8, 1, 9, 11, 7, 2] 0 #[1, 8, 2, 9, 11, 7, 10] (4, 2)
  checkCase "deep-one-child" #[10, 2, 3, 1] 0 #[2, 1, 3, 10] (3, 2)
  checkCase "nonroot" #[0, 10, 2, 3, 4, 5, 6] 1 #[0, 3, 2, 10, 4, 5, 6] (2, 1)
  checkCase "far-invalid" #[1, 2, 3] 1000 #[1, 2, 3] (0, 0)

#eval main

end Cslib.Algorithms.Lean.SiftDownCostRuntime
