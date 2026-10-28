/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nPC

/-! # Factory identification Root8[11]- <-> Twelfth[29]- (record r8f:R83-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[11]- <-> Twelfth[29]-. -/
theorem wR8fR83n_ident : sExtra.symm (rhoLocal (identWordLocal wR8fR83nH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR83nG) (generatedAxisGlobalTwelveRepresentative 10) := by
  have hX := (tensorPlanF_actual wR8fR83nHPlan wR8fR83nHPlan_ok (rootEightSrcXL_bnd (w := 72) (by
      norm_num))
    (by rw [wR8fR83nHPlan_word, wR8fR83nH_growth]; norm_num) 32).1
  rw [wR8fR83nHPlan_word] at hX
  have hY := (tensorPlanF_actual wR8fR83nGPlan wR8fR83nGPlan_ok (twelfthSrcXW_bnd (w := 72) (by
      norm_num))
    (by rw [wR8fR83nGPlan_word, wR8fR83nG_growth]; norm_num) 32).1
  rw [wR8fR83nGPlan_word] at hY
  rw [wR8fR83nH_growth] at hX
  rw [wR8fR83nG_growth] at hY
  exact ident_inverse_selfM 9 10 _ _ wR8fR83nL wR8fR83nW (ofList_ok wR8fR83nHT wR8fR83nT_labels.1)
    (ofList_ok wR8fR83nGT wR8fR83nT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by norm_num)
    (by norm_num) wR8fR83nL_actual wR8fR83nW_actual wR8fR83n_hok wR8fR83n_hm wR8fR83n_hp
        wR8fR83n_hn wR8fR83n_ha wR8fR83n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
