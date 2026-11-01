/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPCy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPCx
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPCl0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPCl1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPCl2

/-! # Factory parts (tensor) of the identification Twelfth[13]- <-> Twelfth[13]+ (record
gtwelfth:W13+, e = 1)

The tensor part of the pairing from its parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source list in groups. -/
theorem twGtwelfthW13pHT_groups : twGtwelfthW13pHT = twGtwelfthW13pHTg0 ++ (twGtwelfthW13pHTg1 ++
    (twGtwelfthW13pHTg2)) := by
  simp only [twGtwelfthW13pHT, twGtwelfthW13pHTg0, twGtwelfthW13pHTg1, twGtwelfthW13pHTg2,
      List.append_assoc]

/-- The tensor part equals the tensor self part of the target. -/
theorem twGtwelfthW13p_ht : twGtwelfthW13pL.sden * (oddLZ 80 true twGtwelfthW13pGX twGtwelfthW13pL
    : ℚ) / ((tensorWordDenAll twGtwelfthW13pG : ℚ) * 32) + (tdotM 80 (trialityTensorT 80 (!true)
    twGtwelfthW13pHX) twGtwelfthW13pGX : ℚ) / (2 * ((tensorWordDenAll twGtwelfthW13pH : ℚ) * 32) *
    ((tensorWordDenAll twGtwelfthW13pG : ℚ) * 32)) = (tdotM 80 twGtwelfthW13pGX twGtwelfthW13pGX :
    ℚ) / (((tensorWordDenAll twGtwelfthW13pG : ℚ) * 32) * ((tensorWordDenAll twGtwelfthW13pG : ℚ)
    * 32)) := by
  have hz : oddLZ 80 true twGtwelfthW13pGX twGtwelfthW13pL = 745275392 + (759169024 + (592707584))
      := by
    unfold twGtwelfthW13pL
    rw [oddLZ_ofList, twGtwelfthW13pHT_groups, oddSumL_append, oddSumL_append, twGtwelfthW13p_ol0,
        twGtwelfthW13p_ol1, twGtwelfthW13p_ol2]
  have hd0 : tensorWordDenAll twGtwelfthW13pG = 8192 := by decide +kernel
  have hd1 : tensorWordDenAll twGtwelfthW13pH = 4096 := by decide +kernel
  rw [hz, twGtwelfthW13p_tx, twGtwelfthW13p_ty, hd0, hd1]
  norm_num [twGtwelfthW13pL]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
