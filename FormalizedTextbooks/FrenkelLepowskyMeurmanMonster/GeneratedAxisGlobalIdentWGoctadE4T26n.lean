/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nPC

/-! # Factory identification Eighth[8]- <-> Tenth[40]+ (record goctad:E4@T26-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGoctadE4T26nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[8]- <-> Tenth[40]+. -/
theorem wGoctadE4T26n_ident : sExtra.symm (rhoLocal (identWordLocal wGoctadE4T26nH)
    (generatedAxisGlobalTwelveRepresentative 7)) =
      rhoLocal (identWordLocal wGoctadE4T26nG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_selfM 7 11 _ _ wGoctadE4T26nL wGoctadE4T26nW (ofList_ok wGoctadE4T26nHT
      wGoctadE4T26nT_labels.1)
    (ofList_ok wGoctadE4T26nGT wGoctadE4T26nT_labels.2) (wGoctadE4T26nHX0_ten ((tensorWordDenAll
        wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))).symm
        (wGoctadE4T26nGX0_ten ((tensorWordDenAll wGoctadE4T26nG : ℚ) * 32)).symm
        wGoctadE4T26nHX0_bnd
    wGoctadE4T26nGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGoctadE4T26nL_actual
        wGoctadE4T26nW_actual wGoctadE4T26n_hok wGoctadE4T26n_hm
    wGoctadE4T26n_hp wGoctadE4T26n_hn wGoctadE4T26n_ha wGoctadE4T26n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
