/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c11nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c11nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c11nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c11nPC

/-! # Factory identification Seventh[18]- <-> Tenth[68]- (record gforest:S7c11-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadXGforestS7c11nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Seventh[18]- <-> Tenth[68]-. -/
theorem wGoctadXGforestS7c11n_ident : sExtra.symm (rhoLocal (identWordLocal wGoctadXGforestS7c11nH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal wGoctadXGforestS7c11nG) (generatedAxisGlobalTwelveRepresentative
          11) :=
  ident_inverse_selfM 6 11 _ _ wGoctadXGforestS7c11nL wGoctadXGforestS7c11nW (ofList_ok
      wGoctadXGforestS7c11nHT wGoctadXGforestS7c11nT_labels.1)
    (ofList_ok wGoctadXGforestS7c11nGT wGoctadXGforestS7c11nT_labels.2)
        (wGoctadXGforestS7c11nHX0_ten ((tensorWordDenAll wGoctadXGforestS7c11nH : ℚ) *
        srcSeventhD0)).symm (wGoctadXGforestS7c11nGX0_ten ((tensorWordDenAll
        wGoctadXGforestS7c11nG : ℚ) * 32)).symm wGoctadXGforestS7c11nHX0_bnd
    wGoctadXGforestS7c11nGX0_bnd (by norm_num) (by norm_num) (by norm_num)
        wGoctadXGforestS7c11nL_actual wGoctadXGforestS7c11nW_actual wGoctadXGforestS7c11n_hok
        wGoctadXGforestS7c11n_hm
    wGoctadXGforestS7c11n_hp wGoctadXGforestS7c11n_hn wGoctadXGforestS7c11n_ha
        wGoctadXGforestS7c11n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
