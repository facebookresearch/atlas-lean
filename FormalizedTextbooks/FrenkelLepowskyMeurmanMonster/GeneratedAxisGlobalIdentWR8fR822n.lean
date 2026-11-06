/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPC

/-! # Factory identification Root8[4]- <-> Root8[4]- (record r8f:R822-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[4]- <-> Root8[4]-. -/
theorem wR8fR822n_ident : sExtra.symm (rhoLocal (identWordLocal wR8fR822nH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR822nG) (generatedAxisGlobalTwelveRepresentative 9) := by
  have hX := (tensorPlanF_actual wR8fR822nHPlan wR8fR822nHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR822nHPlan_word, wR8fR822nH_growth]; norm_num) 32).1
  rw [wR8fR822nHPlan_word] at hX
  have hY := (tensorPlanF_actual wR8fR822nGPlan wR8fR822nGPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR822nGPlan_word, wR8fR822nG_growth]; norm_num) 32).1
  rw [wR8fR822nGPlan_word] at hY
  rw [wR8fR822nH_growth] at hX
  rw [wR8fR822nG_growth] at hY
  exact ident_inverse_selfM 9 9 _ _ wR8fR822nL wR8fR822nW (ofList_ok wR8fR822nHT
      wR8fR822nT_labels.1)
    (ofList_ok wR8fR822nGT wR8fR822nT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by norm_num)
    (by norm_num) wR8fR822nL_actual wR8fR822nW_actual wR8fR822n_hok wR8fR822n_hm wR8fR822n_hp
        wR8fR822n_hn wR8fR822n_ha wR8fR822n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
