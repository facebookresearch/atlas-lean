/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.BalancedThreePhase

@[expose] public section

open PhyslibExt.Circuits.BalancedThreePhase

namespace PhyslibExtTest.Circuits.BalancedThreePhase

/-- Balanced phases carry no neutral current. -/
example (V : ℂ) : neutralCurrent (balancedPhases V) = 0 :=
  neutralCurrent_balancedPhases V

end PhyslibExtTest.Circuits.BalancedThreePhase
