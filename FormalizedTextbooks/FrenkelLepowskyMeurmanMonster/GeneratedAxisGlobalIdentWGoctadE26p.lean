/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pPC

/-! # Factory identification Eighth[37]+ <-> Seventh[32]+ (record goctad:E26+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadE26pTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[37]+ <-> Seventh[32]+. -/
theorem wGoctadE26p_ident : sExtra (rhoLocal (identWordLocal wGoctadE26pH)
    (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal wGoctadE26pG) (generatedAxisGlobalTwelveRepresentative 6) :=
  ident_forward_selfM 7 6 _ _ wGoctadE26pL wGoctadE26pW (ofList_ok wGoctadE26pHT
      wGoctadE26pT_labels.1)
    (ofList_ok wGoctadE26pGT wGoctadE26pT_labels.2) (wGoctadE26pHXn_ten ((tensorWordDenAll
        wGoctadE26pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))).symm
        (wGoctadE26pGXn_ten ((tensorWordDenAll wGoctadE26pG : ℚ) * srcSeventhD0)).symm
        wGoctadE26pHXn_bnd
    wGoctadE26pGXn_bnd (by norm_num) (by norm_num) (by norm_num) wGoctadE26pL_actual
        wGoctadE26pW_actual wGoctadE26p_hok wGoctadE26p_hm
    wGoctadE26p_hp wGoctadE26p_hn wGoctadE26p_ha wGoctadE26p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
