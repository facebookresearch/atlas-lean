/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7pChecks

/-! # The Fourth identification `R7p` (Seventh target): tensor part

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR7pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000 in
/-- The packed tensor dot product of the pairing. -/
theorem fourthR7p_ptdot :
    tdotM 104 (trialityTensorT 104 false fourthR7pHX) fourthR7pGX = 30786325577728 := by
  decide +kernel

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
