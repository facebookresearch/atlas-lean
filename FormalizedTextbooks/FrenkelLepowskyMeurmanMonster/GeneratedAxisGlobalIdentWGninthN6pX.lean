/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXPC

/-! # Factory identification Ninth[10]+ <-> Twelfth[12]- (record gninth:N6+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGninthN6pXTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Ninth[10]+ <-> Twelfth[12]-. -/
theorem wGninthN6pX_ident : sExtra (rhoLocal (identWordLocal wGninthN6pXH)
    (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal (identWordLocal wGninthN6pXG) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_forward_selfM 8 10 _ _ wGninthN6pXL wGninthN6pXW (ofList_ok wGninthN6pXHT
      wGninthN6pXT_labels.1)
    (ofList_ok wGninthN6pXGT wGninthN6pXT_labels.2) (wGninthN6pXHX0_ten ((tensorWordDenAll
        wGninthN6pXH : ℚ) * 32)).symm (wGninthN6pXGX0_ten ((tensorWordDenAll wGninthN6pXG : ℚ) *
        32)).symm wGninthN6pXHX0_bnd
    wGninthN6pXGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGninthN6pXL_actual
        wGninthN6pXW_actual wGninthN6pX_hok wGninthN6pX_hm
    wGninthN6pX_hp wGninthN6pX_hn wGninthN6pX_ha wGninthN6pX_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
