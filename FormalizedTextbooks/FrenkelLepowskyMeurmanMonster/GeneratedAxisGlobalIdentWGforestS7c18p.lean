/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c18pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c18pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c18pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c18pPC

/-! # Factory identification Fourth[13]- <-> Seventh[27]+ (record gforest:S7c18+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGforestS7c18pTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Fourth[13]- <-> Seventh[27]+. -/
theorem wGforestS7c18p_ident : sExtra (rhoLocal (identWordLocal wGforestS7c18pH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal wGforestS7c18pG) (generatedAxisGlobalTwelveRepresentative 3) :=
  ident_forward_selfM 6 3 _ _ wGforestS7c18pL wGforestS7c18pW (ofList_ok wGforestS7c18pHT
      wGforestS7c18pT_labels.1)
    (ofList_ok wGforestS7c18pGT wGforestS7c18pT_labels.2) (wGforestS7c18pHX0_ten
        ((tensorWordDenAll wGforestS7c18pH : ℚ) * srcSeventhD0)).symm (wGforestS7c18pGX0_ten
        ((tensorWordDenAll wGforestS7c18pG : ℚ) * 1)).symm wGforestS7c18pHX0_bnd
    wGforestS7c18pGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGforestS7c18pL_actual
        wGforestS7c18pW_actual wGforestS7c18p_hok wGforestS7c18p_hm
    wGforestS7c18p_hp wGforestS7c18p_hn wGforestS7c18p_ha wGforestS7c18p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
