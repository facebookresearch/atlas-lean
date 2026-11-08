/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.Stack.Basic

public meta section

namespace Cslib.Algorithms.Lean.Stack.BasicRuntimeTests

open Cslib.Algorithms.Lean.Stack

private def testPush (name : String) (stack : List Nat) (value : Nat)
    (expected : List Nat) : IO Unit := do
  let actual := push stack value
  unless actual.ret == expected && actual.time == 1 do
    throw (IO.userError s!"{name}: PUSH mismatch {actual.ret}/{actual.time}")
  IO.println s!"STACK_CASE {name} PASS"

private def testPop (name : String) (stack : List Nat)
    (expected : Option (Nat × List Nat)) (cost : Nat) : IO Unit := do
  let actual := pop stack
  unless actual.ret == expected && actual.time == cost do
    throw (IO.userError s!"{name}: POP mismatch {actual.ret}/{actual.time}")
  IO.println s!"STACK_CASE {name} PASS"

private def testTop (name : String) (stack : List Nat)
    (expected : Option Nat) (cost : Nat) : IO Unit := do
  let actual := top stack
  unless actual.ret == expected && actual.time == cost do
    throw (IO.userError s!"{name}: TOP mismatch {actual.ret}/{actual.time}")
  IO.println s!"STACK_CASE {name} PASS"

def main : IO Unit := do
  testPush "push_empty" [] 7 [7]
  testPush "push_order" [8, 3] 7 [7, 8, 3]
  testPush "push_duplicate" [7, 3] 7 [7, 7, 3]
  testPop "pop_underflow" [] none 0
  testPop "pop_singleton" [7] (some (7, [])) 1
  testPop "pop_order" [7, 8, 3] (some (7, [8, 3])) 1
  testPop "pop_duplicate" [7, 7, 3] (some (7, [7, 3])) 1
  testTop "top_underflow" [] none 0
  testTop "top_singleton" [7] (some 7) 1
  testTop "top_order" [7, 8, 3] (some 7) 1
  testTop "top_duplicate" [7, 7, 3] (some 7) 1
  let pushed := push [8, 3] 7
  testPop "push_pop_roundtrip" pushed.ret (some (7, [8, 3])) 1
  testTop "top_then_pop_top" [7, 8, 3] (some 7) 1
  testPop "top_then_pop_pop" [7, 8, 3] (some (7, [8, 3])) 1
  testTop "top_repeat" [7, 8, 3] (some 7) 1

end Cslib.Algorithms.Lean.Stack.BasicRuntimeTests

#eval Cslib.Algorithms.Lean.Stack.BasicRuntimeTests.main
