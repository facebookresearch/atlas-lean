/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.Universal.Code
public meta import CSLibExt.Computability.Machines.Turing.Universal.Code

@[expose] public section

/-!
# Tests for codes of single-tape machines

`#guard` runs of the clocked evaluator `Code.evalSteps` on small coded machines: the empty table
(halts at once), a machine that erases its first cell (trailing blanks are dropped from the output,
inner ones are kept), a bit flipper that walks back to the start of its input (halts after exactly
`3 n + 2` steps on `n` bits), and a machine that runs right forever.
-/

set_option autoImplicit false

open _root_.Turing

namespace CSLibExtTest.Computability.Machines.Turing.Universal

open Cslib.Turing.Universal

/-- The empty table: every state halts at once, so the output is the input. -/
def haltNow : Code := ⟨[]⟩

#guard haltNow.evalSteps [true, false, true] 0 = some [2, 1, 2]
#guard haltNow.evalSteps [] 5 = some []

/-- Erase the first cell, then halt. -/
def eraseFirst : Code := ⟨[[some (1, 2), some (1, 2), some (1, 2)]]⟩

#guard eraseFirst.evalSteps [true, true] 0 = none
#guard eraseFirst.evalSteps [true, true] 1 = some [0, 2]
#guard eraseFirst.evalSteps [true] 1 = some []

/-- Flip every input bit (state `0` writes, state `1` moves right), walk back left to the blank
before the input (state `2`), step onto the first cell and halt (state `3`). -/
def flipBits : Code :=
  ⟨[[some (2, 0), some (1, 4), some (1, 3)], [none, some (0, 1), some (0, 1)],
    [some (3, 1), some (2, 0), some (2, 0)]]⟩

#guard flipBits.evalSteps [true, false] 7 = none
#guard flipBits.evalSteps [true, false] 8 = some [1, 2]
#guard flipBits.evalSteps [true, false] 100 = some [1, 2]
#guard flipBits.evalSteps [false, false, true] 10 = none
#guard flipBits.evalSteps [false, false, true] 11 = some [2, 2, 1]
#guard flipBits.evalSteps [] 1 = none
#guard flipBits.evalSteps [] 2 = some []

/-- Move right forever. -/
def runRight : Code := ⟨[[some (0, 1), some (0, 1), some (0, 1)]]⟩

#guard runRight.evalSteps [true] 50 = none
#guard runRight.evalSteps [] 0 = none

/-- The decoded flipper's `TM0.eval` on `[true, false]`, through the clocked evaluator. -/
example : TM0.eval flipBits.machine (input [true, false]) = Part.some (ListBlank.mk [1, 2]) :=
  Code.eval_eq_some_of_evalSteps_eq_some (T := 8) rfl

/-- The flipper halts within `8` steps on `[true, false]`. -/
example : HaltsWithin flipBits.machine (input [true, false]) 8 :=
  (Code.isSome_evalSteps_iff _ _ _).1 rfl

/-- The flipper does not halt within `7` steps on `[true, false]`. -/
example : ¬HaltsWithin flipBits.machine (input [true, false]) 7 := by
  rw [← Code.isSome_evalSteps_iff]
  decide

/-- The flipper's states are `0`, `1`, `2` and `3`. -/
example : flipBits.states = {0, 1, 2, 3} := by decide

end CSLibExtTest.Computability.Machines.Turing.Universal
