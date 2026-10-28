/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF12nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF12nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF12nPC

/-! # Factory identification Fifth[12]- <-> Fourth[2]- (record gfifth:F12-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Fifth[12]- <-> Fourth[2]-. -/
theorem wGfifthF12n_ident : sExtra.symm (rhoLocal (identWordLocal wGfifthF12nH)
    (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal (identWordLocal wGfifthF12nG) (generatedAxisGlobalTwelveRepresentative 3) := by
  have hX := (tensorWordAll_actual wGfifthF12nH (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [wGfifthF12nH_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual wGfifthF12nG (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [wGfifthF12nG_growth]; norm_num) 1).1
  rw [wGfifthF12nH_growth] at hX
  rw [wGfifthF12nG_growth] at hY
  exact ident_inverse_selfM 4 3 _ _ wGfifthF12nL wGfifthF12nW (ofList_ok wGfifthF12nHT
      wGfifthF12nT_labels.1)
    (ofList_ok wGfifthF12nGT wGfifthF12nT_labels.2) rfl rfl hX (hY) (by norm_num) (by norm_num)
    (by norm_num) wGfifthF12nL_actual wGfifthF12nW_actual wGfifthF12n_hok wGfifthF12n_hm
        wGfifthF12n_hp wGfifthF12n_hn wGfifthF12n_ha wGfifthF12n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
