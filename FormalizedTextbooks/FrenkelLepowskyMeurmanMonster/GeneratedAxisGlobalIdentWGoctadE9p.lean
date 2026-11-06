/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pPC

/-! # Factory identification Eighth[13]+ <-> Seventh[14]+ (record goctad:E9+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadE9pTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[13]+ <-> Seventh[14]+. -/
theorem wGoctadE9p_ident : sExtra (rhoLocal (identWordLocal wGoctadE9pH)
    (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal wGoctadE9pG) (generatedAxisGlobalTwelveRepresentative 6) :=
  ident_forward_selfM 7 6 _ _ wGoctadE9pL wGoctadE9pW (ofList_ok wGoctadE9pHT wGoctadE9pT_labels.1)
    (ofList_ok wGoctadE9pGT wGoctadE9pT_labels.2) (wGoctadE9pHXn_ten ((tensorWordDenAll
        wGoctadE9pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))).symm (wGoctadE9pGXn_ten
        ((tensorWordDenAll wGoctadE9pG : ℚ) * srcSeventhD0)).symm wGoctadE9pHXn_bnd
    wGoctadE9pGXn_bnd (by norm_num) (by norm_num) (by norm_num) wGoctadE9pL_actual
        wGoctadE9pW_actual wGoctadE9p_hok wGoctadE9p_hm
    wGoctadE9p_hp wGoctadE9p_hn wGoctadE9p_ha wGoctadE9p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
