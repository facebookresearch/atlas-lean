/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR88nTPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR88nTPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR88nTPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR88nTPC

/-! # Factory identification Root8[20]- <-> Tenth[69]+ (record r8f:R88-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWR8fR88nTTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[20]- <-> Tenth[69]+. -/
theorem wR8fR88nT_ident : sExtra.symm (rhoLocal (identWordLocal wR8fR88nTH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR88nTG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_selfM 9 11 _ _ wR8fR88nTL wR8fR88nTW (ofList_ok wR8fR88nTHT wR8fR88nTT_labels.1)
    (ofList_ok wR8fR88nTGT wR8fR88nTT_labels.2) (wR8fR88nTHX0_ten ((tensorWordDenAll wR8fR88nTH :
        ℚ) * 32)).symm (wR8fR88nTGX0_ten ((tensorWordDenAll wR8fR88nTG : ℚ) * 32)).symm
        wR8fR88nTHX0_bnd
    wR8fR88nTGX0_bnd (by norm_num) (by norm_num) (by norm_num) wR8fR88nTL_actual wR8fR88nTW_actual
        wR8fR88nT_hok wR8fR88nT_hm
    wR8fR88nT_hp wR8fR88nT_hn wR8fR88nT_ha wR8fR88nT_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
