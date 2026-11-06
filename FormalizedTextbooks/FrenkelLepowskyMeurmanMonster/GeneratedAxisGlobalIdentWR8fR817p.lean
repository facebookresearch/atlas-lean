/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pPC

/-! # Factory identification Root8[26]+ <-> Root8[26]+ (record r8f:R817+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[26]+ <-> Root8[26]+. -/
theorem wR8fR817p_ident : sExtra (rhoLocal (identWordLocal wR8fR817pH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR817pG) (generatedAxisGlobalTwelveRepresentative 9) := by
  have hX := (tensorPlanF_actual wR8fR817pHPlan wR8fR817pHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR817pHPlan_word, wR8fR817pH_growth]; norm_num) 32).1
  rw [wR8fR817pHPlan_word] at hX
  have hY := (tensorPlanF_actual wR8fR817pGPlan wR8fR817pGPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR817pGPlan_word, wR8fR817pG_growth]; norm_num) 32).1
  rw [wR8fR817pGPlan_word] at hY
  rw [wR8fR817pH_growth] at hX
  rw [wR8fR817pG_growth] at hY
  exact ident_forward_selfM 9 9 _ _ wR8fR817pL wR8fR817pW (ofList_ok wR8fR817pHT
      wR8fR817pT_labels.1)
    (ofList_ok wR8fR817pGT wR8fR817pT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by norm_num)
    (by norm_num) wR8fR817pL_actual wR8fR817pW_actual wR8fR817p_hok wR8fR817p_hm wR8fR817p_hp
        wR8fR817p_hn wR8fR817p_ha wR8fR817p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
