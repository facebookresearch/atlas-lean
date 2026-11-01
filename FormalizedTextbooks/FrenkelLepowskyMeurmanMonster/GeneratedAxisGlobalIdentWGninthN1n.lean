/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nPC

/-! # Factory identification Ninth[1]- <-> Tenth[33]+ (record gninth:N1-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Ninth[1]- <-> Tenth[33]+. -/
theorem wGninthN1n_ident : sExtra.symm (rhoLocal (identWordLocal wGninthN1nH)
    (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal (identWordLocal wGninthN1nG) (generatedAxisGlobalTwelveRepresentative 11) := by
  have hX := (tensorWordAll_actual wGninthN1nH (ninthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wGninthN1nH_growth]; norm_num) 32).1
  have hY := (tensorPlanF_actual wGninthN1nGPlan wGninthN1nGPlan_ok (tenthSrcXL_bnd (w := 64) (by
      norm_num))
    (by rw [wGninthN1nGPlan_word, wGninthN1nG_growth]; norm_num) 32).1
  rw [wGninthN1nGPlan_word] at hY
  rw [wGninthN1nH_growth] at hX
  rw [wGninthN1nG_growth] at hY
  exact ident_inverse_selfM 8 11 _ _ wGninthN1nL wGninthN1nW (ofList_ok wGninthN1nHT
      wGninthN1nT_labels.1)
    (ofList_ok wGninthN1nGT wGninthN1nT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by norm_num)
    (by norm_num) wGninthN1nL_actual wGninthN1nW_actual wGninthN1n_hok wGninthN1n_hm wGninthN1n_hp
        wGninthN1n_hn wGninthN1n_ha wGninthN1n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
