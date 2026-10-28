/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c19+ (gforest:S7c19+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c19+. -/
theorem s7c19p_ident : sExtra (rhoLocal (identWordLocal s7c19pH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c19pG) (generatedAxisGlobalTwelveRepresentative 6) := by
  exact ident_forward_selfM 6 6 _ _ s7c19pL s7c19pW (ofList_ok s7c19pHT s7c19pHT_labels)
    (ofList_ok s7c19pGT s7c19pGT_labels) s7c19pL_tenN s7c19pW_tenN s7c19pHXN_bnd s7c19pGXN_bnd (by
        norm_num)
    (by norm_num)
    (by norm_num) s7c19pL_actual s7c19pW_actual s7c19p_hok s7c19p_hm s7c19p_hp s7c19p_hn s7c19p_ha
        s7c19p_ht

/-- The record gforest:S7c19+ as the wrapper hypothesis `SeventhCellIdentPos 19 6 _`. -/
theorem s7c19p_cell : SeventhCellIdentPos 19 6 s7c19pG := by
  unfold SeventhCellIdentPos
  rw [show seventhCellIdent 19 = s7c19pH from rfl]
  exact s7c19p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
