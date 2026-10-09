/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Selection.HireAssistant
public meta import CSLibExt.Algorithms.Lean.Selection.HireAssistant
public meta import Cslib.Algorithms.Lean.TimeM

/-! Executed hiring fixtures checking the manager, history and both fee components. -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private meta def verify (label : String) (xs : List Int) (manager : Option Nat)
    (history : List Nat) (interviews hires : Nat) : IO Unit := do
  let result := hireAssistant xs
  if result.ret.1 != manager then
    throw (IO.userError s!"{label}: manager got {result.ret.1}, expected {manager}")
  if result.ret.2 != history then
    throw (IO.userError s!"{label}: history got {result.ret.2}, expected {history}")
  if result.time.1 != interviews then
    throw (IO.userError s!"{label}: interviews got {result.time.1}, expected {interviews}")
  if result.time.2 != hires then
    throw (IO.userError s!"{label}: hires got {result.time.2}, expected {hires}")
  IO.println s!"{label}: manager={result.ret.1}, history={result.ret.2}, fees={result.time}"

#eval verify "mixed" [3, 1, 4, 2, 5] (some 4) [0, 2, 4] 5 3
#eval verify "empty" [] none [] 0 0
#eval verify "singleton signed" [-7] (some 0) [0] 1 1
#eval verify "ties" [3, 3, 1, 4, 4] (some 3) [0, 3] 5 2
#eval verify "all equal" [-2, -2, -2] (some 0) [0] 3 1
#eval verify "signed" [-5, -8, -3, -4, -1] (some 4) [0, 2, 4] 5 3
#eval verify "increasing" [-2, -1, 0, 1] (some 3) [0, 1, 2, 3] 4 4
#eval verify "decreasing" [4, 3, 2, 1] (some 0) [0] 4 1
#eval verify "early maximum" [8, 1, 5, 3] (some 0) [0] 4 1
#eval verify "late maximum" [2, 1, 3, 5] (some 3) [0, 2, 3] 4 3
#eval verify "alternating" [1, 0, 2, 1, 3, 2, 4] (some 6) [0, 2, 4, 6] 7 4
#eval verify "adjacent hires" [1, 2, 3, 0] (some 2) [0, 1, 2] 4 3

end Cslib.Algorithms.Lean.TimeM
