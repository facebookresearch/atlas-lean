/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pPC

/-! # Factory identification Eighth[24]+ <-> Tenth[61]+ (record goctad:E19@T33+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadE19T33pTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[24]+ <-> Tenth[61]+. -/
theorem wGoctadE19T33p_ident : sExtra (rhoLocal (identWordLocal wGoctadE19T33pH)
    (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal wGoctadE19T33pG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_selfM 7 11 _ _ wGoctadE19T33pL wGoctadE19T33pW (ofList_ok wGoctadE19T33pHT
      wGoctadE19T33pT_labels.1)
    (ofList_ok wGoctadE19T33pGT wGoctadE19T33pT_labels.2) (wGoctadE19T33pHX0_ten
        ((tensorWordDenAll wGoctadE19T33pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
        1)))).symm (wGoctadE19T33pGX0_ten ((tensorWordDenAll wGoctadE19T33pG : ℚ) * 32)).symm
        wGoctadE19T33pHX0_bnd
    wGoctadE19T33pGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGoctadE19T33pL_actual
        wGoctadE19T33pW_actual wGoctadE19T33p_hok wGoctadE19T33p_hm
    wGoctadE19T33p_hp wGoctadE19T33p_hn wGoctadE19T33p_ha wGoctadE19T33p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
