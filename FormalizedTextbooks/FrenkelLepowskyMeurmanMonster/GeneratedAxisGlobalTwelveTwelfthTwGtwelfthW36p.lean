/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pPC

/-! # Factory identification Twelfth[36]+ <-> Twelfth[36]+ (record gtwelfth:W36+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Twelfth[36]+ <-> Twelfth[36]+. -/
theorem twGtwelfthW36p_ident : sExtra (rhoLocal (identWordLocal twGtwelfthW36pH)
    (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal twGtwelfthW36pG) (generatedAxisGlobalTwelveRepresentative 10) := by
  have hX := (tensorPlanF_actual twGtwelfthW36pHPlan twGtwelfthW36pHPlan_ok (twelfthSrcXW_bnd (w
      := 64) (by norm_num))
    (by rw [twGtwelfthW36pHPlan_word, twGtwelfthW36pH_growth]; norm_num) 32).1
  rw [twGtwelfthW36pHPlan_word] at hX
  have hY := (tensorPlanF_actual twGtwelfthW36pGPlan twGtwelfthW36pGPlan_ok (twelfthSrcXW_bnd (w
      := 64) (by norm_num))
    (by rw [twGtwelfthW36pGPlan_word, twGtwelfthW36pG_growth]; norm_num) 32).1
  rw [twGtwelfthW36pGPlan_word] at hY
  rw [twGtwelfthW36pH_growth] at hX
  rw [twGtwelfthW36pG_growth] at hY
  exact ident_forward_selfM 10 10 _ _ twGtwelfthW36pL twGtwelfthW36pW (ofList_ok twGtwelfthW36pHT
      twGtwelfthW36pT_labels.1)
    (ofList_ok twGtwelfthW36pGT twGtwelfthW36pT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by
        norm_num)
    (by norm_num) twGtwelfthW36pL_actual twGtwelfthW36pW_actual twGtwelfthW36p_hok
        twGtwelfthW36p_hm twGtwelfthW36p_hp twGtwelfthW36p_hn twGtwelfthW36p_ha twGtwelfthW36p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
