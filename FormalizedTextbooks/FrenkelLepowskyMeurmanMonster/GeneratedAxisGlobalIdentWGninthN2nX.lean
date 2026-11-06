/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXPC

/-! # Factory identification Ninth[3]- <-> Tenth[50]+ (record gninth:N2-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGninthN2nXTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Ninth[3]- <-> Tenth[50]+. -/
theorem wGninthN2nX_ident : sExtra.symm (rhoLocal (identWordLocal wGninthN2nXH)
    (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal (identWordLocal wGninthN2nXG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_selfM 8 11 _ _ wGninthN2nXL wGninthN2nXW (ofList_ok wGninthN2nXHT
      wGninthN2nXT_labels.1)
    (ofList_ok wGninthN2nXGT wGninthN2nXT_labels.2) (wGninthN2nXHX0_ten ((tensorWordDenAll
        wGninthN2nXH : ℚ) * 32)).symm (wGninthN2nXGX0_ten ((tensorWordDenAll wGninthN2nXG : ℚ) *
        32)).symm wGninthN2nXHX0_bnd
    wGninthN2nXGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGninthN2nXL_actual
        wGninthN2nXW_actual wGninthN2nX_hok wGninthN2nX_hm
    wGninthN2nX_hp wGninthN2nX_hn wGninthN2nX_ha wGninthN2nX_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
