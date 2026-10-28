/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF0nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF0nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF0nPC

/-! # Factory identification Fifth[0]- <-> Fifth[0]- (record gfifth:F0-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Fifth[0]- <-> Fifth[0]-. -/
theorem wGfifthF0n_ident : sExtra.symm (rhoLocal (identWordLocal wGfifthF0nH)
    (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal (identWordLocal wGfifthF0nG) (generatedAxisGlobalTwelveRepresentative 4) := by
  have hX := (tensorWordAll_actual wGfifthF0nH (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [wGfifthF0nH_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual wGfifthF0nG (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [wGfifthF0nG_growth]; norm_num) 1).1
  rw [wGfifthF0nH_growth] at hX
  rw [wGfifthF0nG_growth] at hY
  exact ident_inverse_selfM 4 4 _ _ wGfifthF0nL wGfifthF0nW (ofList_ok wGfifthF0nHT
      wGfifthF0nT_labels.1)
    (ofList_ok wGfifthF0nGT wGfifthF0nT_labels.2) rfl rfl hX (tbnd_tight 64 24 _ wGfifthF0nGX hY
        (by norm_num) wGfifthF0n_ylt) (by norm_num) (by norm_num)
    (by norm_num) wGfifthF0nL_actual wGfifthF0nW_actual wGfifthF0n_hok wGfifthF0n_hm wGfifthF0n_hp
        wGfifthF0n_hn wGfifthF0n_ha wGfifthF0n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
