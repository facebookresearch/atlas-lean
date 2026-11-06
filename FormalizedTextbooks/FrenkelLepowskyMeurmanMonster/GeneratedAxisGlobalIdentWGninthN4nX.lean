/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXPC

/-! # Factory identification Ninth[6]- <-> Tenth[74]- (record gninth:N4-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGninthN4nXTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Ninth[6]- <-> Tenth[74]-. -/
theorem wGninthN4nX_ident : sExtra.symm (rhoLocal (identWordLocal wGninthN4nXH)
    (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal (identWordLocal wGninthN4nXG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_selfM 8 11 _ _ wGninthN4nXL wGninthN4nXW (ofList_ok wGninthN4nXHT
      wGninthN4nXT_labels.1)
    (ofList_ok wGninthN4nXGT wGninthN4nXT_labels.2) (wGninthN4nXHX0_ten ((tensorWordDenAll
        wGninthN4nXH : ℚ) * 32)).symm (wGninthN4nXGX0_ten ((tensorWordDenAll wGninthN4nXG : ℚ) *
        32)).symm wGninthN4nXHX0_bnd
    wGninthN4nXGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGninthN4nXL_actual
        wGninthN4nXW_actual wGninthN4nX_hok wGninthN4nX_hm
    wGninthN4nX_hp wGninthN4nX_hn wGninthN4nX_ha wGninthN4nX_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
