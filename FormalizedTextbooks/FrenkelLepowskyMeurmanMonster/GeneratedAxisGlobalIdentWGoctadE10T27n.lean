/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE10T27nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE10T27nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE10T27nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE10T27nPC

/-! # Factory identification Eighth[14]- <-> Tenth[55]- (record goctad:E10@T27-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadE10T27nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[14]- <-> Tenth[55]-. -/
theorem wGoctadE10T27n_ident : sExtra.symm (rhoLocal (identWordLocal wGoctadE10T27nH)
    (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal wGoctadE10T27nG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_selfM 7 11 _ _ wGoctadE10T27nL wGoctadE10T27nW (ofList_ok wGoctadE10T27nHT
      wGoctadE10T27nT_labels.1)
    (ofList_ok wGoctadE10T27nGT wGoctadE10T27nT_labels.2) (wGoctadE10T27nHX0_ten
        ((tensorWordDenAll wGoctadE10T27nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
        1)))).symm (wGoctadE10T27nGX0_ten ((tensorWordDenAll wGoctadE10T27nG : ℚ) * 32)).symm
        wGoctadE10T27nHX0_bnd
    wGoctadE10T27nGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGoctadE10T27nL_actual
        wGoctadE10T27nW_actual wGoctadE10T27n_hok wGoctadE10T27n_hm
    wGoctadE10T27n_hp wGoctadE10T27n_hn wGoctadE10T27n_ha wGoctadE10T27n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
