/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPCy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPCx
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPCl0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPCl1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPCl2

/-! # Factory parts (tensor) of the identification Twelfth[9]+ <-> Twelfth[21]- (record
gtwelfth:W9+, e = 1)

The tensor part of the pairing from its parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source list in groups. -/
theorem twGtwelfthW9pHT_groups : twGtwelfthW9pHT = twGtwelfthW9pHTg0 ++ (twGtwelfthW9pHTg1 ++
    (twGtwelfthW9pHTg2)) := by
  simp only [twGtwelfthW9pHT, twGtwelfthW9pHTg0, twGtwelfthW9pHTg1, twGtwelfthW9pHTg2,
      List.append_assoc]

/-- The tensor part equals the tensor self part of the target. -/
theorem twGtwelfthW9p_ht : twGtwelfthW9pL.sden * (oddLZ 80 true twGtwelfthW9pGX twGtwelfthW9pL :
    ℚ) / ((tensorWordDenAll twGtwelfthW9pG : ℚ) * 32) + (tdotM 80 (trialityTensorT 80 (!true)
    twGtwelfthW9pHX) twGtwelfthW9pGX : ℚ) / (2 * ((tensorWordDenAll twGtwelfthW9pH : ℚ) * 32) *
    ((tensorWordDenAll twGtwelfthW9pG : ℚ) * 32)) = (tdotM 80 twGtwelfthW9pGX twGtwelfthW9pGX : ℚ)
    / (((tensorWordDenAll twGtwelfthW9pG : ℚ) * 32) * ((tensorWordDenAll twGtwelfthW9pG : ℚ) *
    32)) := by
  have hz : oddLZ 80 true twGtwelfthW9pGX twGtwelfthW9pL = 744226816 + (760217600 + (592707584))
      := by
    unfold twGtwelfthW9pL
    rw [oddLZ_ofList, twGtwelfthW9pHT_groups, oddSumL_append, oddSumL_append, twGtwelfthW9p_ol0,
        twGtwelfthW9p_ol1, twGtwelfthW9p_ol2]
  have hd0 : tensorWordDenAll twGtwelfthW9pG = 8192 := by decide +kernel
  have hd1 : tensorWordDenAll twGtwelfthW9pH = 4096 := by decide +kernel
  rw [hz, twGtwelfthW9p_tx, twGtwelfthW9p_ty, hd0, hd1]
  norm_num [twGtwelfthW9pL]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
