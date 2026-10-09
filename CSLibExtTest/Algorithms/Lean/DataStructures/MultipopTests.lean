/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.DataStructures.Stack.Multipop

@[expose] public meta section

namespace Cslib.Algorithms.Lean.Stack.MultipopTests

open Cslib.Algorithms.Lean.Stack

private def runCases (args : List String) : IO Unit := do
  let signedCases : List (String × List Nat × Int × List Nat × Nat) :=
    [("Figure16.1 first", [23, 17, 6, 39, 10, 47], 4, [10, 47], 4),
     ("Figure16.1 second", [10, 47], 7, [], 2),
     ("zero count", [23, 17], 0, [23, 17], 0),
     ("empty", [], 7, [], 0),
     ("singleton", [23], 1, [], 1),
     ("duplicate payloads", [23, 23, 17, 17], 2, [17, 17], 2),
     ("negative count", [23, 17], -7, [23, 17], 0),
     ("negative empty", [], -1, [], 0)]
  for (label, stack, k, expected, expectedTime) in signedCases do
    let actual := multipopSigned stack k
    if actual.ret != expected then
      throw <| IO.userError s!"{label}: expected {expected}, actual {actual.ret}"
    if actual.time != expectedTime then
      throw <| IO.userError s!"{label}: expected {expectedTime} pops, actual {actual.time}"
    IO.println s!"{label}: stack={actual.ret}; pops={actual.time}"
  let traceCases : List (String × List Nat × List (Operation Nat) × Option (List Nat) × Nat) :=
    [("retained stack", [], [.push 23, .push 17, .push 6, .multipop 1], some [17, 23], 4),
     ("drained stack", [], [.push 23, .push 17, .push 6, .multipop 2, .pop], some [], 6),
     ("empty POP stops", [], [.pop, .push 23], none, 0),
     ("later empty POP", [23], [.pop, .pop, .push 17], none, 1),
     ("early exhaustion", [23], [.multipop 7, .push 17], some [17], 2),
     ("negative request", [23, 17], [.multipop (-7)], some [23, 17], 0),
     ("empty MULTIPOP", [], [.multipop 7], some [], 0),
     ("duplicate payloads trace", [], [.push 23, .push 23, .multipop 1], some [23], 3)]
  for (label, stack, ops, expected, expectedTime) in traceCases do
    let actual := execute stack ops
    let expected := if args == ["wrong-order"] then expected.map List.reverse else expected
    let expected := if args == ["wrong-underflow"] && expected.isNone then some [] else expected
    if actual.ret != expected then
      throw <| IO.userError s!"{label}: expected {expected}, actual {actual.ret}"
    let expectedTime := if args == ["wrong-count"] then expectedTime + 1 else expectedTime
    if actual.time != expectedTime then
      throw <| IO.userError s!"{label}: expected {expectedTime} events, actual {actual.time}"
    IO.println s!"{label}: stack={actual.ret}; events={actual.time}"

#eval runCases []

end Cslib.Algorithms.Lean.Stack.MultipopTests

end
