/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXPC

/-! # Factory identification Ninth[6]+ <-> Tenth[74]- (record gninth:N4+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGninthN4pXTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Ninth[6]+ <-> Tenth[74]-. -/
theorem wGninthN4pX_ident : sExtra (rhoLocal (identWordLocal wGninthN4pXH)
    (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal (identWordLocal wGninthN4pXG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_selfM 8 11 _ _ wGninthN4pXL wGninthN4pXW (ofList_ok wGninthN4pXHT
      wGninthN4pXT_labels.1)
    (ofList_ok wGninthN4pXGT wGninthN4pXT_labels.2) (wGninthN4pXHX0_ten ((tensorWordDenAll
        wGninthN4pXH : ℚ) * 32)).symm (wGninthN4pXGX0_ten ((tensorWordDenAll wGninthN4pXG : ℚ) *
        32)).symm wGninthN4pXHX0_bnd
    wGninthN4pXGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGninthN4pXL_actual
        wGninthN4pXW_actual wGninthN4pX_hok wGninthN4pX_hm
    wGninthN4pX_hp wGninthN4pX_hn wGninthN4pX_ha wGninthN4pX_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
