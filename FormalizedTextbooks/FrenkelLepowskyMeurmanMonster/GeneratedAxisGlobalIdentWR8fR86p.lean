/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPC

/-! # Factory identification Root8[12]+ <-> Twelfth[34]- (record r8f:R86+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[12]+ <-> Twelfth[34]-. -/
theorem wR8fR86p_ident : sExtra (rhoLocal (identWordLocal wR8fR86pH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR86pG) (generatedAxisGlobalTwelveRepresentative 10) := by
  have hX := (tensorPlanF_actual wR8fR86pHPlan wR8fR86pHPlan_ok (rootEightSrcXL_bnd (w := 96) (by
      norm_num))
    (by rw [wR8fR86pHPlan_word, wR8fR86pH_growth]; norm_num) 32).1
  rw [wR8fR86pHPlan_word] at hX
  have hY := (tensorPlanF_actual wR8fR86pGPlan wR8fR86pGPlan_ok (twelfthSrcXW_bnd (w := 96) (by
      norm_num))
    (by rw [wR8fR86pGPlan_word, wR8fR86pG_growth]; norm_num) 32).1
  rw [wR8fR86pGPlan_word] at hY
  rw [wR8fR86pH_growth] at hX
  rw [wR8fR86pG_growth] at hY
  exact ident_forward_selfM 9 10 _ _ wR8fR86pL wR8fR86pW (ofList_ok wR8fR86pHT wR8fR86pT_labels.1)
    (ofList_ok wR8fR86pGT wR8fR86pT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by norm_num)
    (by norm_num) wR8fR86pL_actual wR8fR86pW_actual wR8fR86p_hok wR8fR86p_hm wR8fR86p_hp
        wR8fR86p_hn wR8fR86p_ha wR8fR86p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
