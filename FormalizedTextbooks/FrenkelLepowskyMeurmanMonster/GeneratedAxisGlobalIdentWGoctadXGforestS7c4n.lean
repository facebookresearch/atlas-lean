/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c4nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c4nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c4nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c4nPC

/-! # Factory identification Seventh[9]- <-> Tenth[1]+ (record gforest:S7c4-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadXGforestS7c4nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Seventh[9]- <-> Tenth[1]+. -/
theorem wGoctadXGforestS7c4n_ident : sExtra.symm (rhoLocal (identWordLocal wGoctadXGforestS7c4nH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal wGoctadXGforestS7c4nG) (generatedAxisGlobalTwelveRepresentative 11)
          :=
  ident_inverse_selfM 6 11 _ _ wGoctadXGforestS7c4nL wGoctadXGforestS7c4nW (ofList_ok
      wGoctadXGforestS7c4nHT wGoctadXGforestS7c4nT_labels.1)
    (ofList_ok wGoctadXGforestS7c4nGT wGoctadXGforestS7c4nT_labels.2) (wGoctadXGforestS7c4nHX0_ten
        ((tensorWordDenAll wGoctadXGforestS7c4nH : ℚ) * srcSeventhD0)).symm
        (wGoctadXGforestS7c4nGX0_ten ((tensorWordDenAll wGoctadXGforestS7c4nG : ℚ) * 32)).symm
        wGoctadXGforestS7c4nHX0_bnd
    wGoctadXGforestS7c4nGX0_bnd (by norm_num) (by norm_num) (by norm_num)
        wGoctadXGforestS7c4nL_actual wGoctadXGforestS7c4nW_actual wGoctadXGforestS7c4n_hok
        wGoctadXGforestS7c4n_hm
    wGoctadXGforestS7c4n_hp wGoctadXGforestS7c4n_hn wGoctadXGforestS7c4n_ha wGoctadXGforestS7c4n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
