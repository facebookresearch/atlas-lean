/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12pPC

/-! # Factory identification Root8[10]- <-> Seventh[19]+ (record gforest:S7c12+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGforestS7c12pTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[10]- <-> Seventh[19]+. -/
theorem wGforestS7c12p_ident : sExtra (rhoLocal (identWordLocal wGforestS7c12pH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal wGforestS7c12pG) (generatedAxisGlobalTwelveRepresentative 9) :=
  ident_forward_selfM 6 9 _ _ wGforestS7c12pL wGforestS7c12pW (ofList_ok wGforestS7c12pHT
      wGforestS7c12pT_labels.1)
    (ofList_ok wGforestS7c12pGT wGforestS7c12pT_labels.2) (wGforestS7c12pHX0_ten
        ((tensorWordDenAll wGforestS7c12pH : ℚ) * srcSeventhD0)).symm (wGforestS7c12pGX0_ten
        ((tensorWordDenAll wGforestS7c12pG : ℚ) * 32)).symm wGforestS7c12pHX0_bnd
    wGforestS7c12pGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGforestS7c12pL_actual
        wGforestS7c12pW_actual wGforestS7c12p_hok wGforestS7c12p_hm
    wGforestS7c12p_hp wGforestS7c12p_hn wGforestS7c12p_ha wGforestS7c12p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
