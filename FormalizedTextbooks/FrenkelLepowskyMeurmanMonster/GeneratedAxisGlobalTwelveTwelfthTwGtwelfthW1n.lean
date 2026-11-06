/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nPC

/-! # Factory identification Twelfth[1]- <-> Twelfth[1]+ (record gtwelfth:W1-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Twelfth[1]- <-> Twelfth[1]+. -/
theorem twGtwelfthW1n_ident : sExtra.symm (rhoLocal (identWordLocal twGtwelfthW1nH)
    (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal twGtwelfthW1nG) (generatedAxisGlobalTwelveRepresentative 10) := by
  have hX := (tensorPlanF_actual twGtwelfthW1nHPlan twGtwelfthW1nHPlan_ok (twelfthSrcXW_bnd (w :=
      64) (by norm_num))
    (by rw [twGtwelfthW1nHPlan_word, twGtwelfthW1nH_growth]; norm_num) 32).1
  rw [twGtwelfthW1nHPlan_word] at hX
  have hY := (tensorPlanF_actual twGtwelfthW1nGPlan twGtwelfthW1nGPlan_ok (twelfthSrcXW_bnd (w :=
      64) (by norm_num))
    (by rw [twGtwelfthW1nGPlan_word, twGtwelfthW1nG_growth]; norm_num) 32).1
  rw [twGtwelfthW1nGPlan_word] at hY
  rw [twGtwelfthW1nH_growth] at hX
  rw [twGtwelfthW1nG_growth] at hY
  exact ident_inverse_selfM 10 10 _ _ twGtwelfthW1nL twGtwelfthW1nW (ofList_ok twGtwelfthW1nHT
      twGtwelfthW1nT_labels.1)
    (ofList_ok twGtwelfthW1nGT twGtwelfthW1nT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by
        norm_num)
    (by norm_num) twGtwelfthW1nL_actual twGtwelfthW1nW_actual twGtwelfthW1n_hok twGtwelfthW1n_hm
        twGtwelfthW1n_hp twGtwelfthW1n_hn twGtwelfthW1n_ha twGtwelfthW1n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
