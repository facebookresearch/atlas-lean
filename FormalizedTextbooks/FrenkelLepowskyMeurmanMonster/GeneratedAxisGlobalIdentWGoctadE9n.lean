/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nPC

/-! # Factory identification Eighth[13]- <-> Eighth[13]- (record goctad:E9-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadE9nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[13]- <-> Eighth[13]-. -/
theorem wGoctadE9n_ident : sExtra.symm (rhoLocal (identWordLocal wGoctadE9nH)
    (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal wGoctadE9nG) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_inverse_selfM 7 7 _ _ wGoctadE9nL wGoctadE9nW (ofList_ok wGoctadE9nHT wGoctadE9nT_labels.1)
    (ofList_ok wGoctadE9nGT wGoctadE9nT_labels.2) (wGoctadE9nHXn_ten ((tensorWordDenAll
        wGoctadE9nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))).symm (wGoctadE9nGXn_ten
        ((tensorWordDenAll wGoctadE9nG : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))).symm
        wGoctadE9nHXn_bnd
    wGoctadE9nGXn_bnd (by norm_num) (by norm_num) (by norm_num) wGoctadE9nL_actual
        wGoctadE9nW_actual wGoctadE9n_hok wGoctadE9n_hm
    wGoctadE9n_hp wGoctadE9n_hn wGoctadE9n_ha wGoctadE9n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
