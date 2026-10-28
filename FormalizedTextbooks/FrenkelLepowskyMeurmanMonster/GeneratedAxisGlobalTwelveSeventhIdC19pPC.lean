/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pNTH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pNTG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib

/-! # Parts (tensor) of the identification Seventh cell record S7c19+ (gforest:S7c19+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor denominator of the source word. -/
theorem s7c19pH_denC : tensorWordDenAll s7c19pH = 4096 := by decide

/-- The tensor denominator of the target word. -/
theorem s7c19pG_den : tensorWordDenAll s7c19pG = 8192 := by decide

set_option maxRecDepth 100000 in
/-- The odd short terms of the source against the target tensor, the self dot of the target tensor,
and the fields of the target tensor are below `2^25` (one kernel evaluation of the target
tensor). -/
theorem s7c19p_hty : oddLZ 72 true s7c19pGXN s7c19pL = 33397665693696 ∧ tdotM 72 s7c19pGXN
    s7c19pGXN = 547187354725515264 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The tensor dot of the triality image of the source tensor with the target tensor. -/
theorem s7c19p_htc : tdotM 72 (trialityTensorT 72 (!true) s7c19pHXN) s7c19pGXN =
    273593677362757632 := by
  decide +kernel

/-- The tensor part equals the tensor self part of the target. -/
theorem s7c19p_ht : s7c19pL.sden * (oddLZ 72 true s7c19pGXN s7c19pL : ℚ) / ((tensorWordDenAll
    s7c19pG : ℚ) * srcSeventhD0) +
    (tdotM 72 (trialityTensorT 72 (!true) s7c19pHXN) s7c19pGXN : ℚ) / (2 * ((tensorWordDenAll
        s7c19pH : ℚ) * srcSeventhD0) * ((tensorWordDenAll s7c19pG : ℚ) * srcSeventhD0)) =
      (tdotM 72 s7c19pGXN s7c19pGXN : ℚ) / (((tensorWordDenAll s7c19pG : ℚ) * srcSeventhD0) *
          ((tensorWordDenAll s7c19pG : ℚ) * srcSeventhD0)) := by
  rw [s7c19p_hty.1, s7c19p_hty.2, s7c19p_htc]
  show 1 / srcSeventhD0 * ((33397665693696 : ℤ) : ℚ) / ((tensorWordDenAll s7c19pG : ℚ) *
      srcSeventhD0) +
      ((273593677362757632 : ℤ) : ℚ) / (2 * ((tensorWordDenAll s7c19pH : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c19pG : ℚ) * srcSeventhD0)) =
      ((547187354725515264 : ℤ) : ℚ) / (((tensorWordDenAll s7c19pG : ℚ) * srcSeventhD0) *
        ((tensorWordDenAll s7c19pG : ℚ) * srcSeventhD0))
  rw [s7c19pH_denC, s7c19pG_den]
  norm_num [srcSeventhD0_eq]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
