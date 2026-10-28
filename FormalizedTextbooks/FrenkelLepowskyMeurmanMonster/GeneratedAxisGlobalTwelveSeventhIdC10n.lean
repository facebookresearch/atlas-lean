/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c10- (gforest:S7c10-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c10-. -/
theorem s7c10n_ident : sExtra.symm (rhoLocal (identWordLocal s7c10nH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c10nG) (generatedAxisGlobalTwelveRepresentative 9) := by
  exact ident_inverse_selfM 6 9 _ _ s7c10nL s7c10nW (ofList_ok s7c10nHT s7c10nHT_labels)
    (ofList_ok s7c10nGT s7c10nGT_labels) s7c10nL_tenN s7c10nW_tenN s7c10nHXN_bnd s7c10nGXN_bnd (by
        norm_num)
    (by norm_num)
    (by norm_num) s7c10nL_actual s7c10nW_actual s7c10n_hok s7c10n_hm s7c10n_hp s7c10n_hn s7c10n_ha
        s7c10n_ht

/-- The record gforest:S7c10- as the wrapper hypothesis `SeventhCellIdentNeg 10 9 _`. -/
theorem s7c10n_cell : SeventhCellIdentNeg 10 9 s7c10nG := by
  unfold SeventhCellIdentNeg
  rw [show seventhCellIdent 10 = s7c10nH from rfl]
  exact s7c10n_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
