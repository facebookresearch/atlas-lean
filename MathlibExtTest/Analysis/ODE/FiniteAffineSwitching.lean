/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.FiniteAffineSwitching

@[expose] public section

open MathlibExt.Analysis.ODE.FiniteAffineSwitching

namespace MathlibExtTest.Analysis.ODE.FiniteAffineSwitching

/-- The two-level fixture is a genuine switched trajectory. -/
example : IsSwitchedTrajectory twoLevelA twoLevelForcing twoLevelTimes 0 twoLevelTrajectory :=
  twoLevel_isSwitchedTrajectory

/-- The reset trajectory is not a switched trajectory. -/
example : ¬ IsSwitchedTrajectory twoLevelA twoLevelForcing twoLevelTimes 0 resetTrajectory :=
  reset_not_continuousOn.2.2

end MathlibExtTest.Analysis.ODE.FiniteAffineSwitching
