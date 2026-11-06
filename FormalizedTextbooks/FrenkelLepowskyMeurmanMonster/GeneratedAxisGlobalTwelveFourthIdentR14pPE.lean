/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOddZ

/-! # The Fourth identification `R14p` (Seventh target): odd short part

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR14pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The odd short terms of the Seventh image against the Fourth image (integer form). -/
theorem fourthR14p_psoddZ : oddWZ 104 true fourthR14pHX fourthR14pW = 117440512 := by
  decide +kernel

/-- The odd terms of the short part of the pairing. -/
theorem fourthR14p_psodd :
    (fourthR14pW.sh.odd.map (fun q => (q.2 : ℚ) * triOddF true fourthR14pL q.1)).sum =
      229376 := by
  have hd : tensorWordDenAll fourthR14pH = 256 := by decide
  rw [oddW_packed 104 true fourthR14pL fourthR14pW fourthR14pHX ((tensorWordDenAll fourthR14pH : ℚ) * 1) rfl, fourthR14p_psoddZ, hd]
  norm_num

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
