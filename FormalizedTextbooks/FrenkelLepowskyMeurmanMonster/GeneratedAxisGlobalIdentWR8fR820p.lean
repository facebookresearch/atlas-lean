/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820pPC

/-! # Factory identification Fourth[10]+ <-> Root8[25]+ (record r8f:R820+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Fourth[10]+ <-> Root8[25]+. -/
theorem wR8fR820p_ident : sExtra (rhoLocal (identWordLocal wR8fR820pH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR820pG) (generatedAxisGlobalTwelveRepresentative 3) := by
  have hX := (tensorWordAll_actual wR8fR820pH (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wR8fR820pH_growth]; norm_num) 32).1
  have hY := (tensorPlanF_actual wR8fR820pGPlan wR8fR820pGPlan_ok (fourthSrcXW_bnd (w := 64) (by
      norm_num))
    (by rw [wR8fR820pGPlan_word, wR8fR820pG_growth]; norm_num) 1).1
  rw [wR8fR820pGPlan_word] at hY
  rw [wR8fR820pH_growth] at hX
  rw [wR8fR820pG_growth] at hY
  exact ident_forward_selfM 9 3 _ _ wR8fR820pL wR8fR820pW (ofList_ok wR8fR820pHT
      wR8fR820pT_labels.1)
    (ofList_ok wR8fR820pGT wR8fR820pT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by norm_num)
    (by norm_num) wR8fR820pL_actual wR8fR820pW_actual wR8fR820p_hok wR8fR820p_hm wR8fR820p_hp
        wR8fR820p_hn wR8fR820p_ha wR8fR820p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
