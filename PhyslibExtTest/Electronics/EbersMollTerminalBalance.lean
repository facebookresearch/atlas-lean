/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.EbersMollTerminalBalance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Electronics.EbersMollTerminalBalance

namespace PhyslibExtTest.Electronics.EbersMollTerminalBalance

/-- Terminal currents balance at the nonzero bias point of the
next example: collector plus base minus emitter is zero. -/
example : collectorCurrent 2 3 (1 / 2) 1 (Real.log 2) 0
    + baseCurrent 2 3 (1 / 2) (1 / 3) 1 (Real.log 2) 0
    - emitterCurrent 2 3 (1 / 3) 1 (Real.log 2) 0 = 0 :=
  terminal_current_balance 2 3 (1 / 2) (1 / 3) 1 (Real.log 2) 0

/-- A genuinely nonzero exact case: `VT = 1`, `Vbe = log 2`,
`Vbc = 0` gives branch currents `F = 2`, `R = 0`, hence
`Ic = 1`, `Ib = 1`, `Ie = 2` and balance `1 + 1 - 2 = 0`. This
detects wrong signs and gain placement, unlike the zero-bias
cases. -/
example : collectorCurrent 2 3 (1 / 2) 1 (Real.log 2) 0 = 1
    ∧ baseCurrent 2 3 (1 / 2) (1 / 3) 1 (Real.log 2) 0 = 1
    ∧ emitterCurrent 2 3 (1 / 3) 1 (Real.log 2) 0 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [collectorCurrent, baseCurrent, emitterCurrent, forwardBranchCurrent,
      reverseBranchCurrent, Real.exp_log] <;> norm_num

/-- At zero bias the collector current vanishes. -/
example : collectorCurrent 2 3 1 1 0 0 = 0 :=
  (terminalCurrents_zero_bias 2 3 1 1 1).1

/-- At zero bias the base current vanishes. -/
example : baseCurrent 2 3 1 1 1 0 0 = 0 :=
  (terminalCurrents_zero_bias 2 3 1 1 1).2.1

/-- At zero bias the emitter current vanishes. -/
example : emitterCurrent 2 3 1 1 0 0 = 0 :=
  (terminalCurrents_zero_bias 2 3 1 1 1).2.2

/-- Saturation-region exact case: `VT = 1`, `Vbe = log 2`,
`Vbc = log 3` (both junctions forward biased) gives branch
currents `F = 2`, `R = 2`, hence `Ic = -1`, `Ib = 7/3`,
`Ie = 4/3`. The reverse branch and `alphaR` are genuinely
exercised (unlike `Vbc = 0`). -/
example : collectorCurrent 2 1 (1 / 2) 1 (Real.log 2) (Real.log 3) = -1
    ∧ baseCurrent 2 1 (1 / 2) (1 / 3) 1 (Real.log 2) (Real.log 3) = 7 / 3
    ∧ emitterCurrent 2 1 (1 / 3) 1 (Real.log 2) (Real.log 3) = 4 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [collectorCurrent, baseCurrent, emitterCurrent, forwardBranchCurrent,
      reverseBranchCurrent, Real.exp_log] <;> norm_num

end PhyslibExtTest.Electronics.EbersMollTerminalBalance
