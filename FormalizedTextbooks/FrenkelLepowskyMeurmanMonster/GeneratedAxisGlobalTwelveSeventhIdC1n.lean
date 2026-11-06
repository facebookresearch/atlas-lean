/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c1- (gforest:S7c1-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c1-. -/
theorem s7c1n_ident : sExtra.symm (rhoLocal (identWordLocal s7c1nH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c1nG) (generatedAxisGlobalTwelveRepresentative 6) := by
  exact ident_inverse_selfM 6 6 _ _ s7c1nL s7c1nW (ofList_ok s7c1nHT s7c1nHT_labels)
    (ofList_ok s7c1nGT s7c1nGT_labels) s7c1nL_tenN s7c1nW_tenN s7c1nHXN_bnd s7c1nGXN_bnd (by
        norm_num)
    (by norm_num)
    (by norm_num) s7c1nL_actual s7c1nW_actual s7c1n_hok s7c1n_hm s7c1n_hp s7c1n_hn s7c1n_ha s7c1n_ht

/-- The record gforest:S7c1- as the wrapper hypothesis `SeventhCellIdentNeg 1 6 _`. -/
theorem s7c1n_cell : SeventhCellIdentNeg 1 6 s7c1nG := by
  unfold SeventhCellIdentNeg
  rw [show seventhCellIdent 1 = s7c1nH from rfl]
  exact s7c1n_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
