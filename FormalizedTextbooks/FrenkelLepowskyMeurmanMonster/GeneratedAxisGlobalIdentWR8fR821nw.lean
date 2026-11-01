/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwPC

/-! # Factory identification Root8[33]- <-> Root8[33]- (record r8f:R821-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[33]- <-> Root8[33]-. -/
theorem wR8fR821nw_ident : sExtra.symm (rhoLocal (identWordLocal wR8fR821nwH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR821nwG) (generatedAxisGlobalTwelveRepresentative 9) := by
  have hX := (tensorPlanF_actual wR8fR821nwHPlan wR8fR821nwHPlan_ok (rootEightSrcXL_bnd (w := 96)
      (by norm_num))
    (by rw [wR8fR821nwHPlan_word, wR8fR821nwH_growth]; norm_num) 32).1
  rw [wR8fR821nwHPlan_word] at hX
  have hY := (tensorPlanF_actual wR8fR821nwGPlan wR8fR821nwGPlan_ok (rootEightSrcXL_bnd (w := 96)
      (by norm_num))
    (by rw [wR8fR821nwGPlan_word, wR8fR821nwG_growth]; norm_num) 32).1
  rw [wR8fR821nwGPlan_word] at hY
  rw [wR8fR821nwH_growth] at hX
  rw [wR8fR821nwG_growth] at hY
  exact ident_inverse_selfM 9 9 _ _ wR8fR821nwL wR8fR821nwW (ofList_ok wR8fR821nwHT
      wR8fR821nwT_labels.1)
    (ofList_ok wR8fR821nwGT wR8fR821nwT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by norm_num)
    (by norm_num) wR8fR821nwL_actual wR8fR821nwW_actual wR8fR821nw_hok wR8fR821nw_hm wR8fR821nw_hp
        wR8fR821nw_hn wR8fR821nw_ha wR8fR821nw_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
