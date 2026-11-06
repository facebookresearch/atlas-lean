/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pPC

/-! # Factory identification Twelfth[9]+ <-> Twelfth[21]- (record gtwelfth:W9+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Twelfth[9]+ <-> Twelfth[21]-. -/
theorem twGtwelfthW9p_ident : sExtra (rhoLocal (identWordLocal twGtwelfthW9pH)
    (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal twGtwelfthW9pG) (generatedAxisGlobalTwelveRepresentative 10) := by
  have hX := (tensorPlanF_actual twGtwelfthW9pHPlan twGtwelfthW9pHPlan_ok (twelfthSrcXW_bnd (w :=
      80) (by norm_num))
    (by rw [twGtwelfthW9pHPlan_word, twGtwelfthW9pH_growth]; norm_num) 32).1
  rw [twGtwelfthW9pHPlan_word] at hX
  have hY := (tensorPlanF_actual twGtwelfthW9pGPlan twGtwelfthW9pGPlan_ok (twelfthSrcXW_bnd (w :=
      80) (by norm_num))
    (by rw [twGtwelfthW9pGPlan_word, twGtwelfthW9pG_growth]; norm_num) 32).1
  rw [twGtwelfthW9pGPlan_word] at hY
  rw [twGtwelfthW9pH_growth] at hX
  rw [twGtwelfthW9pG_growth] at hY
  exact ident_forward_selfM 10 10 _ _ twGtwelfthW9pL twGtwelfthW9pW (ofList_ok twGtwelfthW9pHT
      twGtwelfthW9pT_labels.1)
    (ofList_ok twGtwelfthW9pGT twGtwelfthW9pT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by
        norm_num)
    (by norm_num) twGtwelfthW9pL_actual twGtwelfthW9pW_actual twGtwelfthW9p_hok twGtwelfthW9p_hm
        twGtwelfthW9p_hp twGtwelfthW9p_hn twGtwelfthW9p_ha twGtwelfthW9p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
