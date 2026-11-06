/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTPC

/-! # Factory identification Root8[22]+ <-> Root8[22]+ (record r8f:R816+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWR8fR816pTTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[22]+ <-> Root8[22]+. -/
theorem wR8fR816pT_ident : sExtra (rhoLocal (identWordLocal wR8fR816pTH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR816pTG) (generatedAxisGlobalTwelveRepresentative 9) :=
  ident_forward_selfM 9 9 _ _ wR8fR816pTL wR8fR816pTW (ofList_ok wR8fR816pTHT wR8fR816pTT_labels.1)
    (ofList_ok wR8fR816pTGT wR8fR816pTT_labels.2) (wR8fR816pTHX0_ten ((tensorWordDenAll
        wR8fR816pTH : ℚ) * 32)).symm (wR8fR816pTGX0_ten ((tensorWordDenAll wR8fR816pTG : ℚ) *
        32)).symm wR8fR816pTHX0_bnd
    wR8fR816pTGX0_bnd (by norm_num) (by norm_num) (by norm_num) wR8fR816pTL_actual
        wR8fR816pTW_actual wR8fR816pT_hok wR8fR816pT_hm
    wR8fR816pT_hp wR8fR816pT_hn wR8fR816pT_ha wR8fR816pT_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
