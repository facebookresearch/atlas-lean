/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC1nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC1nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC1nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC1nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdent

/-! # The identification Sixth cell record S6c1- (gforest:S6c1-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S6c1-. -/
theorem s6c1n_ident : sExtra.symm (rhoLocal (identWordLocal s6c1nH)
    (generatedAxisGlobalTwelveRepresentative 5)) =
      rhoLocal (identWordLocal s6c1nG) (generatedAxisGlobalTwelveRepresentative 6) := by
  exact ident_inverse_selfM 5 6 _ _ s6c1nL s6c1nW (ofList_ok s6c1nHT s6c1nHT_labels)
    (ofList_ok s6c1nGT s6c1nGT_labels) s6c1nL_tenN s6c1nW_tenN s6c1nHXN_bnd s6c1nGXN_bnd (by
        norm_num)
    (by norm_num)
    (by norm_num) s6c1nL_actual s6c1nW_actual s6c1n_hok s6c1n_hm s6c1n_hp s6c1n_hn s6c1n_ha s6c1n_ht

/-- The record gforest:S6c1- as the wrapper hypothesis `SixthCellIdentNeg 1 6 _`. -/
theorem s6c1n_cell : SixthCellIdentNeg 1 6 s6c1nG := by
  unfold SixthCellIdentNeg
  rw [show sixthCellIdent 1 = s6c1nH from rfl]
  exact s6c1n_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
