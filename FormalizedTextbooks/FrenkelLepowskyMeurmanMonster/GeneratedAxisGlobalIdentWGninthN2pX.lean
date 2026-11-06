/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXPC

/-! # Factory identification Ninth[3]+ <-> Tenth[50]+ (record gninth:N2+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGninthN2pXTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Ninth[3]+ <-> Tenth[50]+. -/
theorem wGninthN2pX_ident : sExtra (rhoLocal (identWordLocal wGninthN2pXH)
    (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal (identWordLocal wGninthN2pXG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_selfM 8 11 _ _ wGninthN2pXL wGninthN2pXW (ofList_ok wGninthN2pXHT
      wGninthN2pXT_labels.1)
    (ofList_ok wGninthN2pXGT wGninthN2pXT_labels.2) (wGninthN2pXHX0_ten ((tensorWordDenAll
        wGninthN2pXH : ℚ) * 32)).symm (wGninthN2pXGX0_ten ((tensorWordDenAll wGninthN2pXG : ℚ) *
        32)).symm wGninthN2pXHX0_bnd
    wGninthN2pXGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGninthN2pXL_actual
        wGninthN2pXW_actual wGninthN2pX_hok wGninthN2pX_hm
    wGninthN2pX_hp wGninthN2pX_hn wGninthN2pX_ha wGninthN2pX_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
