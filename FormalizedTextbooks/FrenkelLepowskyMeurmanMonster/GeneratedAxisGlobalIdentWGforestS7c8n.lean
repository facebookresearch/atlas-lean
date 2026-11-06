/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nPC

/-! # Factory identification Eighth[13]+ <-> Seventh[14]- (record gforest:S7c8-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`, with the normalized tensors of
`GeneratedAxisGlobalIdentWGforestS7c8nTX`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Eighth[13]+ <-> Seventh[14]-. -/
theorem wGforestS7c8n_ident : sExtra.symm (rhoLocal (identWordLocal wGforestS7c8nH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal wGforestS7c8nG) (generatedAxisGlobalTwelveRepresentative 7) :=
  ident_inverse_selfM 6 7 _ _ wGforestS7c8nL wGforestS7c8nW (ofList_ok wGforestS7c8nHT
      wGforestS7c8nT_labels.1)
    (ofList_ok wGforestS7c8nGT wGforestS7c8nT_labels.2) (wGforestS7c8nHX0_ten ((tensorWordDenAll
        wGforestS7c8nH : ℚ) * srcSeventhD0)).symm (wGforestS7c8nGX0_ten ((tensorWordDenAll
        wGforestS7c8nG : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1)))).symm
        wGforestS7c8nHX0_bnd
    wGforestS7c8nGX0_bnd (by norm_num) (by norm_num) (by norm_num) wGforestS7c8nL_actual
        wGforestS7c8nW_actual wGforestS7c8n_hok wGforestS7c8n_hm
    wGforestS7c8n_hp wGforestS7c8n_hn wGforestS7c8n_ha wGforestS7c8n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
