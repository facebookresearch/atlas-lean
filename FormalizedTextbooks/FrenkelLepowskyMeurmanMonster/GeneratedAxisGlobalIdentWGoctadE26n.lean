/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26nPC

/-! # Factory identification Eighth[37]- <-> Seventh[1]+ (record goctad:E26-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadE26nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[37]- <-> Seventh[1]+. -/
theorem wGoctadE26n_ident : sExtra.symm (rhoLocal (identWordLocal wGoctadE26nH)
    (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal wGoctadE26nG) (generatedAxisGlobalTwelveRepresentative 6) :=
  ident_inverse_selfM 7 6 _ _ wGoctadE26nL wGoctadE26nW (ofList_ok wGoctadE26nHT
      wGoctadE26nT_labels.1)
    (ofList_ok wGoctadE26nGT wGoctadE26nT_labels.2) (wGoctadE26nHXn_ten ((tensorWordDenAll
        wGoctadE26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))).symm
        (wGoctadE26nGXn_ten ((tensorWordDenAll wGoctadE26nG : ℚ) * srcSeventhD0)).symm
        wGoctadE26nHXn_bnd
    wGoctadE26nGXn_bnd (by norm_num) (by norm_num) (by norm_num) wGoctadE26nL_actual
        wGoctadE26nW_actual wGoctadE26n_hok wGoctadE26n_hm
    wGoctadE26n_hp wGoctadE26n_hn wGoctadE26n_ha wGoctadE26n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
