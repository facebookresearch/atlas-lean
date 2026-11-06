/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pPC

/-! # Factory identification Twelfth[30]- <-> Twelfth[30]+ (record gtwelfth:W30+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Twelfth[30]- <-> Twelfth[30]+. -/
theorem wGtwelfthW30p_ident : sExtra (rhoLocal (identWordLocal wGtwelfthW30pH)
    (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal wGtwelfthW30pG) (generatedAxisGlobalTwelveRepresentative 10) := by
  have hX := (tensorPlanF_actual wGtwelfthW30pHPlan wGtwelfthW30pHPlan_ok (twelfthSrcXW_bnd (w :=
      64) (by norm_num))
    (by rw [wGtwelfthW30pHPlan_word, wGtwelfthW30pH_growth]; norm_num) 32).1
  rw [wGtwelfthW30pHPlan_word] at hX
  have hY := (tensorPlanF_actual wGtwelfthW30pGPlan wGtwelfthW30pGPlan_ok (twelfthSrcXW_bnd (w :=
      64) (by norm_num))
    (by rw [wGtwelfthW30pGPlan_word, wGtwelfthW30pG_growth]; norm_num) 32).1
  rw [wGtwelfthW30pGPlan_word] at hY
  rw [wGtwelfthW30pH_growth] at hX
  rw [wGtwelfthW30pG_growth] at hY
  exact ident_forward_selfM 10 10 _ _ wGtwelfthW30pL wGtwelfthW30pW (ofList_ok wGtwelfthW30pHT
      wGtwelfthW30pT_labels.1)
    (ofList_ok wGtwelfthW30pGT wGtwelfthW30pT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by
        norm_num)
    (by norm_num) wGtwelfthW30pL_actual wGtwelfthW30pW_actual wGtwelfthW30p_hok wGtwelfthW30p_hm
        wGtwelfthW30p_hp wGtwelfthW30p_hn wGtwelfthW30p_ha wGtwelfthW30p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
