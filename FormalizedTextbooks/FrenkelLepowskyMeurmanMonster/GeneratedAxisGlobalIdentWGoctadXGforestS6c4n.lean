/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c4nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c4nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c4nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c4nPC

/-! # Factory identification Sixth[8]- <-> Tenth[73]+ (record gforest:S6c4-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadXGforestS6c4nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Sixth[8]- <-> Tenth[73]+. -/
theorem wGoctadXGforestS6c4n_ident : sExtra.symm (rhoLocal (identWordLocal wGoctadXGforestS6c4nH)
    (generatedAxisGlobalTwelveRepresentative 5)) =
      rhoLocal (identWordLocal wGoctadXGforestS6c4nG) (generatedAxisGlobalTwelveRepresentative 11)
          :=
  ident_inverse_selfM 5 11 _ _ wGoctadXGforestS6c4nL wGoctadXGforestS6c4nW (ofList_ok
      wGoctadXGforestS6c4nHT wGoctadXGforestS6c4nT_labels.1)
    (ofList_ok wGoctadXGforestS6c4nGT wGoctadXGforestS6c4nT_labels.2) (wGoctadXGforestS6c4nHX0_ten
        ((tensorWordDenAll wGoctadXGforestS6c4nH : ℚ) * 32)).symm (wGoctadXGforestS6c4nGX0_ten
        ((tensorWordDenAll wGoctadXGforestS6c4nG : ℚ) * 32)).symm wGoctadXGforestS6c4nHX0_bnd
    wGoctadXGforestS6c4nGX0_bnd (by norm_num) (by norm_num) (by norm_num)
        wGoctadXGforestS6c4nL_actual wGoctadXGforestS6c4nW_actual wGoctadXGforestS6c4n_hok
        wGoctadXGforestS6c4n_hm
    wGoctadXGforestS6c4n_hp wGoctadXGforestS6c4n_hn wGoctadXGforestS6c4n_ha wGoctadXGforestS6c4n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
