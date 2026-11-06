/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR87nTPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR87nTPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR87nTPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR87nTPC

/-! # Factory identification Root8[8]- <-> Tenth[51]- (record r8f:R87-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWR8fR87nTTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[8]- <-> Tenth[51]-. -/
theorem wR8fR87nT_ident : sExtra.symm (rhoLocal (identWordLocal wR8fR87nTH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR87nTG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_selfM 9 11 _ _ wR8fR87nTL wR8fR87nTW (ofList_ok wR8fR87nTHT wR8fR87nTT_labels.1)
    (ofList_ok wR8fR87nTGT wR8fR87nTT_labels.2) (wR8fR87nTHX0_ten ((tensorWordDenAll wR8fR87nTH :
        ℚ) * 32)).symm (wR8fR87nTGX0_ten ((tensorWordDenAll wR8fR87nTG : ℚ) * 32)).symm
        wR8fR87nTHX0_bnd
    wR8fR87nTGX0_bnd (by norm_num) (by norm_num) (by norm_num) wR8fR87nTL_actual wR8fR87nTW_actual
        wR8fR87nT_hok wR8fR87nT_hm
    wR8fR87nT_hp wR8fR87nT_hn wR8fR87nT_ha wR8fR87nT_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
