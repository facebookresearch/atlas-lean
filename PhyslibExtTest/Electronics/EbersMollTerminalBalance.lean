/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.EbersMollTerminalBalance
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Electronics.EbersMollTerminalBalance

namespace PhyslibExtTest.Electronics.EbersMollTerminalBalance

/-- Terminal currents balance at a concrete bias point:
collector plus base minus emitter is zero. -/
example : collectorCurrent 2 3 1 1 0 0 + baseCurrent 2 3 1 1 1 0 0
    - emitterCurrent 2 3 1 1 0 0 = 0 :=
  terminal_current_balance 2 3 1 1 1 0 0

/-- At zero bias the collector current vanishes. -/
example : collectorCurrent 2 3 1 1 0 0 = 0 :=
  (terminalCurrents_zero_bias 2 3 1 1 1).1

/-- At zero bias the base current vanishes. -/
example : baseCurrent 2 3 1 1 1 0 0 = 0 :=
  (terminalCurrents_zero_bias 2 3 1 1 1).2.1

/-- At zero bias the emitter current vanishes. -/
example : emitterCurrent 2 3 1 1 0 0 = 0 :=
  (terminalCurrents_zero_bias 2 3 1 1 1).2.2

end PhyslibExtTest.Electronics.EbersMollTerminalBalance
