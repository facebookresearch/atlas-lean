/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nPC

/-! # Factory identification Eighth[23]- <-> Tenth[58]- (record goctad:E18-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadXGoctadE18nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[23]- <-> Tenth[58]-. -/
theorem wGoctadXGoctadE18n_ident : sExtra.symm (rhoLocal (identWordLocal wGoctadXGoctadE18nH)
    (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal wGoctadXGoctadE18nG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_selfM 7 11 _ _ wGoctadXGoctadE18nL wGoctadXGoctadE18nW (ofList_ok
      wGoctadXGoctadE18nHT wGoctadXGoctadE18nT_labels.1)
    (ofList_ok wGoctadXGoctadE18nGT wGoctadXGoctadE18nT_labels.2) (wGoctadXGoctadE18nHX0_ten
        ((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
        1)))).symm (wGoctadXGoctadE18nGX0_ten ((tensorWordDenAll wGoctadXGoctadE18nG : ℚ) *
        32)).symm wGoctadXGoctadE18nHX0_bnd
    wGoctadXGoctadE18nGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGoctadXGoctadE18nL_actual
        wGoctadXGoctadE18nW_actual wGoctadXGoctadE18n_hok wGoctadXGoctadE18n_hm
    wGoctadXGoctadE18n_hp wGoctadXGoctadE18n_hn wGoctadXGoctadE18n_ha wGoctadXGoctadE18n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
