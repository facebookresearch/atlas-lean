/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR811nTPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR811nTPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR811nTPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR811nTPC

/-! # Factory identification Root8[13]- <-> Root8[13]- (record r8f:R811-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWR8fR811nTTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[13]- <-> Root8[13]-. -/
theorem wR8fR811nT_ident : sExtra.symm (rhoLocal (identWordLocal wR8fR811nTH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR811nTG) (generatedAxisGlobalTwelveRepresentative 9) :=
  ident_inverse_selfM 9 9 _ _ wR8fR811nTL wR8fR811nTW (ofList_ok wR8fR811nTHT wR8fR811nTT_labels.1)
    (ofList_ok wR8fR811nTGT wR8fR811nTT_labels.2) (wR8fR811nTHX0_ten ((tensorWordDenAll
        wR8fR811nTH : ℚ) * 32)).symm (wR8fR811nTGX0_ten ((tensorWordDenAll wR8fR811nTG : ℚ) *
        32)).symm wR8fR811nTHX0_bnd
    wR8fR811nTGX0_bnd (by norm_num) (by norm_num) (by norm_num) wR8fR811nTL_actual
        wR8fR811nTW_actual wR8fR811nT_hok wR8fR811nT_hm
    wR8fR811nT_hp wR8fR811nT_hn wR8fR811nT_ha wR8fR811nT_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
