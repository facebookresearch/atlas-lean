/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pPC

/-! # Factory identification Eighth[46]+ <-> Tenth[46]+ (record goctad:E33@T32+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadE33T32pTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[46]+ <-> Tenth[46]+. -/
theorem wGoctadE33T32p_ident : sExtra (rhoLocal (identWordLocal wGoctadE33T32pH)
    (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal wGoctadE33T32pG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_selfM 7 11 _ _ wGoctadE33T32pL wGoctadE33T32pW (ofList_ok wGoctadE33T32pHT
      wGoctadE33T32pT_labels.1)
    (ofList_ok wGoctadE33T32pGT wGoctadE33T32pT_labels.2) (wGoctadE33T32pHX0_ten
        ((tensorWordDenAll wGoctadE33T32pH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
        1)))).symm (wGoctadE33T32pGX0_ten ((tensorWordDenAll wGoctadE33T32pG : ℚ) * 32)).symm
        wGoctadE33T32pHX0_bnd
    wGoctadE33T32pGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGoctadE33T32pL_actual
        wGoctadE33T32pW_actual wGoctadE33T32p_hok wGoctadE33T32p_hm
    wGoctadE33T32p_hp wGoctadE33T32p_hn wGoctadE33T32p_ha wGoctadE33T32p_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
