/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pPC

/-! # Factory identification Eighth[27]+ <-> Seventh[22]+ (record gforest:S7c14+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGforestS7c14pTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[27]+ <-> Seventh[22]+. -/
theorem wGforestS7c14p_ident : sExtra (rhoLocal (identWordLocal wGforestS7c14pH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal wGforestS7c14pG) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_forward_selfM 6 7 _ _ wGforestS7c14pL wGforestS7c14pW (ofList_ok wGforestS7c14pHT
      wGforestS7c14pT_labels.1)
    (ofList_ok wGforestS7c14pGT wGforestS7c14pT_labels.2) (wGforestS7c14pHX0_ten
        ((tensorWordDenAll wGforestS7c14pH : ℚ) * srcSeventhD0)).symm (wGforestS7c14pGX0_ten
        ((tensorWordDenAll wGforestS7c14pG : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
        1)))).symm wGforestS7c14pHX0_bnd
    wGforestS7c14pGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGforestS7c14pL_actual
        wGforestS7c14pW_actual wGforestS7c14p_hok wGforestS7c14p_hm
    wGforestS7c14p_hp wGforestS7c14p_hn wGforestS7c14p_ha wGforestS7c14p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
