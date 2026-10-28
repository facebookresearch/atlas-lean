/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOddZ

/-! # The Fourth identification `R3p` (Twelfth target): odd short part

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR3pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The odd short terms of the Twelfth image against the Fourth image, part 0 (integer form). -/
theorem fourthR3p_psoddZ0 :
    (((fourthR3pW.sh.odd).take 7509).map (fun q => q.2 * oddWTerm 64 true fourthR3pHX q.1)).sum = 585024 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd short terms of the Twelfth image against the Fourth image, part 1 (integer form). -/
theorem fourthR3p_psoddZ1 :
    (((((fourthR3pW.sh.odd).drop 7509)).take 7509).map (fun q => q.2 * oddWTerm 64 true fourthR3pHX q.1)).sum = 671040 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd short terms of the Twelfth image against the Fourth image, part 2 (integer form). -/
theorem fourthR3p_psoddZ2 :
    (((((fourthR3pW.sh.odd).drop 7509)).drop 7509).map (fun q => q.2 * oddWTerm 64 true fourthR3pHX q.1)).sum = 578944 := by
  decide +kernel

/-- The odd short terms of the Twelfth image against the Fourth image (integer form). -/
theorem fourthR3p_psoddZ : oddWZ 64 true fourthR3pHX fourthR3pW = 585024 + 671040 + 578944 := by
  unfold oddWZ
  rw [← List.take_append_drop 7509 (fourthR3pW.sh.odd), List.map_append, List.sum_append, fourthR3p_psoddZ0,
    ← List.take_append_drop 7509 ((fourthR3pW.sh.odd).drop 7509), List.map_append, List.sum_append, fourthR3p_psoddZ1,
    fourthR3p_psoddZ2]
  norm_num

/-- The odd terms of the short part of the pairing. -/
theorem fourthR3p_psodd :
    (fourthR3pW.sh.odd.map (fun q => (q.2 : ℚ) * triOddF true fourthR3pL q.1)).sum =
      3584 := by
  have hd : tensorWordDenAll fourthR3pH = 256 := by decide
  rw [oddW_packed 64 true fourthR3pL fourthR3pW fourthR3pHX ((tensorWordDenAll fourthR3pH : ℚ) * 1) rfl, fourthR3p_psoddZ, hd]
  norm_num

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
