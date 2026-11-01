/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPCy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPCx
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPCl0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPCl1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPCl2

/-! # Factory parts (tensor) of the identification Twelfth[9]+ <-> Twelfth[21]+ (record
gtwelfth:W21+, e = 1)

The tensor part of the pairing from its parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source list in groups. -/
theorem twGtwelfthW21pHT_groups : twGtwelfthW21pHT = twGtwelfthW21pHTg0 ++ (twGtwelfthW21pHTg1 ++
    (twGtwelfthW21pHTg2)) := by
  simp only [twGtwelfthW21pHT, twGtwelfthW21pHTg0, twGtwelfthW21pHTg1, twGtwelfthW21pHTg2,
      List.append_assoc]

/-- The tensor part equals the tensor self part of the target. -/
theorem twGtwelfthW21p_ht : twGtwelfthW21pL.sden * (oddLZ 80 true twGtwelfthW21pGX twGtwelfthW21pL
    : ℚ) / ((tensorWordDenAll twGtwelfthW21pG : ℚ) * 32) + (tdotM 80 (trialityTensorT 80 (!true)
    twGtwelfthW21pHX) twGtwelfthW21pGX : ℚ) / (2 * ((tensorWordDenAll twGtwelfthW21pH : ℚ) * 32) *
    ((tensorWordDenAll twGtwelfthW21pG : ℚ) * 32)) = (tdotM 80 twGtwelfthW21pGX twGtwelfthW21pGX :
    ℚ) / (((tensorWordDenAll twGtwelfthW21pG : ℚ) * 32) * ((tensorWordDenAll twGtwelfthW21pG : ℚ)
    * 32)) := by
  have hz : oddLZ 80 true twGtwelfthW21pGX twGtwelfthW21pL = 736886784 + (767557632 + (592707584))
      := by
    unfold twGtwelfthW21pL
    rw [oddLZ_ofList, twGtwelfthW21pHT_groups, oddSumL_append, oddSumL_append, twGtwelfthW21p_ol0,
        twGtwelfthW21p_ol1, twGtwelfthW21p_ol2]
  have hd0 : tensorWordDenAll twGtwelfthW21pG = 8192 := by decide +kernel
  have hd1 : tensorWordDenAll twGtwelfthW21pH = 4096 := by decide +kernel
  rw [hz, twGtwelfthW21p_tx, twGtwelfthW21p_ty, hd0, hd1]
  norm_num [twGtwelfthW21pL]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
