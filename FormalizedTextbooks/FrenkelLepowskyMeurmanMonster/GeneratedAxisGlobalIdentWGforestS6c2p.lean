/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c2pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c2pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c2pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c2pPC

/-! # Factory identification Fourth[18]- <-> Sixth[3]+ (record gforest:S6c2+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGforestS6c2pTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Fourth[18]- <-> Sixth[3]+. -/
theorem wGforestS6c2p_ident : sExtra (rhoLocal (identWordLocal wGforestS6c2pH)
    (generatedAxisGlobalTwelveRepresentative 5)) =
      rhoLocal (identWordLocal wGforestS6c2pG) (generatedAxisGlobalTwelveRepresentative 3) :=
  ident_forward_selfM 5 3 _ _ wGforestS6c2pL wGforestS6c2pW (ofList_ok wGforestS6c2pHT
      wGforestS6c2pT_labels.1)
    (ofList_ok wGforestS6c2pGT wGforestS6c2pT_labels.2) (wGforestS6c2pHX0_ten ((tensorWordDenAll
        wGforestS6c2pH : ℚ) * 32)).symm (wGforestS6c2pGX0_ten ((tensorWordDenAll wGforestS6c2pG :
        ℚ) * 1)).symm wGforestS6c2pHX0_bnd
    wGforestS6c2pGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGforestS6c2pL_actual
        wGforestS6c2pW_actual wGforestS6c2p_hok wGforestS6c2p_hm
    wGforestS6c2p_hp wGforestS6c2p_hn wGforestS6c2p_ha wGforestS6c2p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
