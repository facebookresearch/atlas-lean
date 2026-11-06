/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXPC

/-! # Factory identification Fifth[4]+ <-> Ninth[12]- (record gninth:N7-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGninthN7nXTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Fifth[4]+ <-> Ninth[12]-. -/
theorem wGninthN7nX_ident : sExtra.symm (rhoLocal (identWordLocal wGninthN7nXH)
    (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal (identWordLocal wGninthN7nXG) (generatedAxisGlobalTwelveRepresentative 4) :=
  ident_inverse_selfM 8 4 _ _ wGninthN7nXL wGninthN7nXW (ofList_ok wGninthN7nXHT
      wGninthN7nXT_labels.1)
    (ofList_ok wGninthN7nXGT wGninthN7nXT_labels.2) (wGninthN7nXHX0_ten ((tensorWordDenAll
        wGninthN7nXH : ℚ) * 32)).symm (wGninthN7nXGX0_ten ((tensorWordDenAll wGninthN7nXG : ℚ) *
        1)).symm wGninthN7nXHX0_bnd
    wGninthN7nXGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGninthN7nXL_actual
        wGninthN7nXW_actual wGninthN7nX_hok wGninthN7nX_hm
    wGninthN7nX_hp wGninthN7nX_hn wGninthN7nX_ha wGninthN7nX_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
