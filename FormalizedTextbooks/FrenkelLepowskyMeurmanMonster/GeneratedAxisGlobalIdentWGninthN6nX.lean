/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6nXPC

/-! # Factory identification Ninth[10]- <-> Twelfth[12]- (record gninth:N6-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGninthN6nXTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Ninth[10]- <-> Twelfth[12]-. -/
theorem wGninthN6nX_ident : sExtra.symm (rhoLocal (identWordLocal wGninthN6nXH)
    (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal (identWordLocal wGninthN6nXG) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_inverse_selfM 8 10 _ _ wGninthN6nXL wGninthN6nXW (ofList_ok wGninthN6nXHT
      wGninthN6nXT_labels.1)
    (ofList_ok wGninthN6nXGT wGninthN6nXT_labels.2) (wGninthN6nXHX0_ten ((tensorWordDenAll
        wGninthN6nXH : ℚ) * 32)).symm (wGninthN6nXGX0_ten ((tensorWordDenAll wGninthN6nXG : ℚ) *
        32)).symm wGninthN6nXHX0_bnd
    wGninthN6nXGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGninthN6nXL_actual
        wGninthN6nXW_actual wGninthN6nX_hok wGninthN6nX_hm
    wGninthN6nX_hp wGninthN6nX_hn wGninthN6nX_ha wGninthN6nX_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
