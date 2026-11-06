/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82nTPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82nTPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82nTPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82nTPC

/-! # Factory identification Root8[2]- <-> Tenth[38]+ (record r8f:R82-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWR8fR82nTTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[2]- <-> Tenth[38]+. -/
theorem wR8fR82nT_ident : sExtra.symm (rhoLocal (identWordLocal wR8fR82nTH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR82nTG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_selfM 9 11 _ _ wR8fR82nTL wR8fR82nTW (ofList_ok wR8fR82nTHT wR8fR82nTT_labels.1)
    (ofList_ok wR8fR82nTGT wR8fR82nTT_labels.2) (wR8fR82nTHX0_ten ((tensorWordDenAll wR8fR82nTH :
        ℚ) * 32)).symm (wR8fR82nTGX0_ten ((tensorWordDenAll wR8fR82nTG : ℚ) * 32)).symm
        wR8fR82nTHX0_bnd
    wR8fR82nTGX0_bnd (by norm_num) (by norm_num) (by norm_num) wR8fR82nTL_actual wR8fR82nTW_actual
        wR8fR82nT_hok wR8fR82nT_hm
    wR8fR82nT_hp wR8fR82nT_hn wR8fR82nT_ha wR8fR82nT_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
