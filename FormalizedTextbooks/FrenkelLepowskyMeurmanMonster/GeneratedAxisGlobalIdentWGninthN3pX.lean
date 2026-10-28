/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXPC

/-! # Factory identification Ninth[5]+ <-> Twelfth[31]+ (record gninth:N3+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGninthN3pXTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Ninth[5]+ <-> Twelfth[31]+. -/
theorem wGninthN3pX_ident : sExtra (rhoLocal (identWordLocal wGninthN3pXH)
    (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal (identWordLocal wGninthN3pXG) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_forward_selfM 8 10 _ _ wGninthN3pXL wGninthN3pXW (ofList_ok wGninthN3pXHT
      wGninthN3pXT_labels.1)
    (ofList_ok wGninthN3pXGT wGninthN3pXT_labels.2) (wGninthN3pXHX0_ten ((tensorWordDenAll
        wGninthN3pXH : ℚ) * 32)).symm (wGninthN3pXGX0_ten ((tensorWordDenAll wGninthN3pXG : ℚ) *
        32)).symm wGninthN3pXHX0_bnd
    wGninthN3pXGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGninthN3pXL_actual
        wGninthN3pXW_actual wGninthN3pX_hok wGninthN3pX_hm
    wGninthN3pX_hp wGninthN3pX_hn wGninthN3pX_ha wGninthN3pX_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
