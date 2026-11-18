/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Instrumentation.HeldDACSettling
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Instrumentation.DACLevelError
open PhyslibExt.Instrumentation.HeldDACSettling

namespace PhyslibExtTest.Instrumentation.HeldDACSettling

/-- At zero elapsed time the settling output is the initial
value, with exponential factor one: `settlingOutput 5 2 3 7 3`
is `2`, and its deviation from the held level `5` is the initial
mismatch `-3` times `exp 0`. -/
example : settlingOutput 5 2 3 7 3 = 2 ∧
    settlingOutput 5 2 3 7 3 - 5 =
      (2 - 5) * Real.exp (-(3 - 3 : ℝ) / 7) := by
  constructor
  · exact settlingOutput_at_start 5 2 3 7
  · simp [settlingOutput]

/-- Concrete converter levels: a zero-error level with step
`2` at code `3` is `6`, and a level with step `1 / 2` and error
`k / 10` at code `4` is `12 / 5`. -/
example : dacLevel 2 (fun _ => 0) 3 = 6 ∧
    dacLevel (1 / 2) (fun k => (k : ℝ) / 10) 4 = 12 / 5 := by
  constructor <;> simp only [dacLevel] <;> norm_num

end PhyslibExtTest.Instrumentation.HeldDACSettling
