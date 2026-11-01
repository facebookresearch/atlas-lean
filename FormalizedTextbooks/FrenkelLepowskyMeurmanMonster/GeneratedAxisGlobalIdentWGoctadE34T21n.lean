/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nPC

/-! # Factory identification Eighth[47]- <-> Tenth[26]+ (record goctad:E34@T21-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadE34T21nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[47]- <-> Tenth[26]+. -/
theorem wGoctadE34T21n_ident : sExtra.symm (rhoLocal (identWordLocal wGoctadE34T21nH)
    (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal wGoctadE34T21nG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_selfM 7 11 _ _ wGoctadE34T21nL wGoctadE34T21nW (ofList_ok wGoctadE34T21nHT
      wGoctadE34T21nT_labels.1)
    (ofList_ok wGoctadE34T21nGT wGoctadE34T21nT_labels.2) (wGoctadE34T21nHX0_ten
        ((tensorWordDenAll wGoctadE34T21nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) *
        1)))).symm (wGoctadE34T21nGX0_ten ((tensorWordDenAll wGoctadE34T21nG : ℚ) * 32)).symm
        wGoctadE34T21nHX0_bnd
    wGoctadE34T21nGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGoctadE34T21nL_actual
        wGoctadE34T21nW_actual wGoctadE34T21n_hok wGoctadE34T21n_hm
    wGoctadE34T21n_hp wGoctadE34T21n_hn wGoctadE34T21n_ha wGoctadE34T21n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
