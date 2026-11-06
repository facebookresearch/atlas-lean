/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pPC

/-! # Factory identification Twelfth[9]+ <-> Twelfth[21]+ (record gtwelfth:W21+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Twelfth[9]+ <-> Twelfth[21]+. -/
theorem twGtwelfthW21p_ident : sExtra (rhoLocal (identWordLocal twGtwelfthW21pH)
    (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal twGtwelfthW21pG) (generatedAxisGlobalTwelveRepresentative 10) := by
  have hX := (tensorPlanF_actual twGtwelfthW21pHPlan twGtwelfthW21pHPlan_ok (twelfthSrcXW_bnd (w
      := 80) (by norm_num))
    (by rw [twGtwelfthW21pHPlan_word, twGtwelfthW21pH_growth]; norm_num) 32).1
  rw [twGtwelfthW21pHPlan_word] at hX
  have hY := (tensorPlanF_actual twGtwelfthW21pGPlan twGtwelfthW21pGPlan_ok (twelfthSrcXW_bnd (w
      := 80) (by norm_num))
    (by rw [twGtwelfthW21pGPlan_word, twGtwelfthW21pG_growth]; norm_num) 32).1
  rw [twGtwelfthW21pGPlan_word] at hY
  rw [twGtwelfthW21pH_growth] at hX
  rw [twGtwelfthW21pG_growth] at hY
  exact ident_forward_selfM 10 10 _ _ twGtwelfthW21pL twGtwelfthW21pW (ofList_ok twGtwelfthW21pHT
      twGtwelfthW21pT_labels.1)
    (ofList_ok twGtwelfthW21pGT twGtwelfthW21pT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by
        norm_num)
    (by norm_num) twGtwelfthW21pL_actual twGtwelfthW21pW_actual twGtwelfthW21p_hok
        twGtwelfthW21p_hm twGtwelfthW21p_hp twGtwelfthW21p_hn twGtwelfthW21p_ha twGtwelfthW21p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
