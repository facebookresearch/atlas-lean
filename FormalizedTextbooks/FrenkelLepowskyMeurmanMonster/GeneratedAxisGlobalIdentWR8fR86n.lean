/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPC

/-! # Factory identification Root8[12]- <-> Twelfth[34]- (record r8f:R86-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[12]- <-> Twelfth[34]-. -/
theorem wR8fR86n_ident : sExtra.symm (rhoLocal (identWordLocal wR8fR86nH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR86nG) (generatedAxisGlobalTwelveRepresentative 10) := by
  have hX := (tensorPlanF_actual wR8fR86nHPlan wR8fR86nHPlan_ok (rootEightSrcXL_bnd (w := 96) (by
      norm_num))
    (by rw [wR8fR86nHPlan_word, wR8fR86nH_growth]; norm_num) 32).1
  rw [wR8fR86nHPlan_word] at hX
  have hY := (tensorPlanF_actual wR8fR86nGPlan wR8fR86nGPlan_ok (twelfthSrcXW_bnd (w := 96) (by
      norm_num))
    (by rw [wR8fR86nGPlan_word, wR8fR86nG_growth]; norm_num) 32).1
  rw [wR8fR86nGPlan_word] at hY
  rw [wR8fR86nH_growth] at hX
  rw [wR8fR86nG_growth] at hY
  exact ident_inverse_selfM 9 10 _ _ wR8fR86nL wR8fR86nW (ofList_ok wR8fR86nHT wR8fR86nT_labels.1)
    (ofList_ok wR8fR86nGT wR8fR86nT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by norm_num)
    (by norm_num) wR8fR86nL_actual wR8fR86nW_actual wR8fR86n_hok wR8fR86n_hm wR8fR86n_hp
        wR8fR86n_hn wR8fR86n_ha wR8fR86n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
