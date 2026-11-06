/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nXPC

/-! # Factory identification Ninth[5]- <-> Twelfth[31]+ (record gninth:N3-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGninthN3nXTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Ninth[5]- <-> Twelfth[31]+. -/
theorem wGninthN3nX_ident : sExtra.symm (rhoLocal (identWordLocal wGninthN3nXH)
    (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal (identWordLocal wGninthN3nXG) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_inverse_selfM 8 10 _ _ wGninthN3nXL wGninthN3nXW (ofList_ok wGninthN3nXHT
      wGninthN3nXT_labels.1)
    (ofList_ok wGninthN3nXGT wGninthN3nXT_labels.2) (wGninthN3nXHX0_ten ((tensorWordDenAll
        wGninthN3nXH : ℚ) * 32)).symm (wGninthN3nXGX0_ten ((tensorWordDenAll wGninthN3nXG : ℚ) *
        32)).symm wGninthN3nXHX0_bnd
    wGninthN3nXGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGninthN3nXL_actual
        wGninthN3nXW_actual wGninthN3nX_hok wGninthN3nX_hm
    wGninthN3nX_hp wGninthN3nX_hn wGninthN3nX_ha wGninthN3nX_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
