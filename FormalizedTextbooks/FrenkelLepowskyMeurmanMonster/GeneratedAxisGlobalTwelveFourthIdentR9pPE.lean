/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR9pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOddZ

/-! # The Fourth identification `R9p` (Eighth target): odd short part

Part of the exact pairing `pairTriGMO` of the two representations of
`GeneratedAxisGlobalTwelveFourthIdentR9pChecks`, evaluated in its own kernel checks (one module
per memory-heavy part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The odd short terms of the Eighth image against the Fourth image, part 0 (integer form). -/
theorem fourthR9p_psoddZ0 :
    (((fourthR9pW.sh.odd).take 7168).map (fun q => q.2 * oddWTerm 88 true fourthR9pHX q.1)).sum = 41943040 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd short terms of the Eighth image against the Fourth image, part 1 (integer form). -/
theorem fourthR9p_psoddZ1 :
    (((((fourthR9pW.sh.odd).drop 7168)).take 7168).map (fun q => q.2 * oddWTerm 88 true fourthR9pHX q.1)).sum = 33554432 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd short terms of the Eighth image against the Fourth image, part 2 (integer form). -/
theorem fourthR9p_psoddZ2 :
    (((((fourthR9pW.sh.odd).drop 7168)).drop 7168).map (fun q => q.2 * oddWTerm 88 true fourthR9pHX q.1)).sum = 41943040 := by
  decide +kernel

/-- The odd short terms of the Eighth image against the Fourth image (integer form). -/
theorem fourthR9p_psoddZ : oddWZ 88 true fourthR9pHX fourthR9pW = 41943040 + 33554432 + 41943040 := by
  unfold oddWZ
  rw [← List.take_append_drop 7168 (fourthR9pW.sh.odd), List.map_append, List.sum_append, fourthR9p_psoddZ0,
    ← List.take_append_drop 7168 ((fourthR9pW.sh.odd).drop 7168), List.map_append, List.sum_append, fourthR9p_psoddZ1,
    fourthR9p_psoddZ2]
  norm_num

/-- The odd terms of the short part of the pairing. -/
theorem fourthR9p_psodd :
    (fourthR9pW.sh.odd.map (fun q => (q.2 : ℚ) * triOddF true fourthR9pL q.1)).sum =
      229376 := by
  have hd : tensorWordDenAll fourthR9pH = 256 := by decide
  rw [oddW_packed 88 true fourthR9pL fourthR9pW fourthR9pHX ((tensorWordDenAll fourthR9pH : ℚ) * 1) rfl, fourthR9p_psoddZ, hd]
  norm_num

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
