/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pPC

/-! # Factory identification Twelfth[13]- <-> Twelfth[13]+ (record gtwelfth:W13+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Twelfth[13]- <-> Twelfth[13]+. -/
theorem twGtwelfthW13p_ident : sExtra (rhoLocal (identWordLocal twGtwelfthW13pH)
    (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal twGtwelfthW13pG) (generatedAxisGlobalTwelveRepresentative 10) := by
  have hX := (tensorPlanF_actual twGtwelfthW13pHPlan twGtwelfthW13pHPlan_ok (twelfthSrcXW_bnd (w
      := 80) (by norm_num))
    (by rw [twGtwelfthW13pHPlan_word, twGtwelfthW13pH_growth]; norm_num) 32).1
  rw [twGtwelfthW13pHPlan_word] at hX
  have hY := (tensorPlanF_actual twGtwelfthW13pGPlan twGtwelfthW13pGPlan_ok (twelfthSrcXW_bnd (w
      := 80) (by norm_num))
    (by rw [twGtwelfthW13pGPlan_word, twGtwelfthW13pG_growth]; norm_num) 32).1
  rw [twGtwelfthW13pGPlan_word] at hY
  rw [twGtwelfthW13pH_growth] at hX
  rw [twGtwelfthW13pG_growth] at hY
  exact ident_forward_selfM 10 10 _ _ twGtwelfthW13pL twGtwelfthW13pW (ofList_ok twGtwelfthW13pHT
      twGtwelfthW13pT_labels.1)
    (ofList_ok twGtwelfthW13pGT twGtwelfthW13pT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by
        norm_num)
    (by norm_num) twGtwelfthW13pL_actual twGtwelfthW13pW_actual twGtwelfthW13p_hok
        twGtwelfthW13p_hm twGtwelfthW13p_hp twGtwelfthW13p_hn twGtwelfthW13p_ha twGtwelfthW13p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
