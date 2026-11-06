/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c17nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c17nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c17nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c17nPC

/-! # Factory identification Seventh[26]- <-> Tenth[66]+ (record gforest:S7c17-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadXGforestS7c17nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Seventh[26]- <-> Tenth[66]+. -/
theorem wGoctadXGforestS7c17n_ident : sExtra.symm (rhoLocal (identWordLocal wGoctadXGforestS7c17nH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal wGoctadXGforestS7c17nG) (generatedAxisGlobalTwelveRepresentative
          11) :=
  ident_inverse_selfM 6 11 _ _ wGoctadXGforestS7c17nL wGoctadXGforestS7c17nW (ofList_ok
      wGoctadXGforestS7c17nHT wGoctadXGforestS7c17nT_labels.1)
    (ofList_ok wGoctadXGforestS7c17nGT wGoctadXGforestS7c17nT_labels.2)
        (wGoctadXGforestS7c17nHX0_ten ((tensorWordDenAll wGoctadXGforestS7c17nH : ℚ) *
        srcSeventhD0)).symm (wGoctadXGforestS7c17nGX0_ten ((tensorWordDenAll
        wGoctadXGforestS7c17nG : ℚ) * 32)).symm wGoctadXGforestS7c17nHX0_bnd
    wGoctadXGforestS7c17nGX0_bnd (by norm_num) (by norm_num) (by norm_num)
        wGoctadXGforestS7c17nL_actual wGoctadXGforestS7c17nW_actual wGoctadXGforestS7c17n_hok
        wGoctadXGforestS7c17n_hm
    wGoctadXGforestS7c17n_hp wGoctadXGforestS7c17n_hn wGoctadXGforestS7c17n_ha
        wGoctadXGforestS7c17n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
