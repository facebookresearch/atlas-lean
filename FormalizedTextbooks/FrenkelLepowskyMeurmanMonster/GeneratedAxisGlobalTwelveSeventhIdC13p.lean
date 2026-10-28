/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC13pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC13pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC13pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC13pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c13+ (gforest:S7c13+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c13+. -/
theorem s7c13p_ident : sExtra (rhoLocal (identWordLocal s7c13pH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c13pG) (generatedAxisGlobalTwelveRepresentative 6) := by
  exact ident_forward_selfM 6 6 _ _ s7c13pL s7c13pW (ofList_ok s7c13pHT s7c13pHT_labels)
    (ofList_ok s7c13pGT s7c13pGT_labels) s7c13pL_tenN s7c13pW_tenN s7c13pHXN_bnd s7c13pGXN_bnd (by
        norm_num)
    (by norm_num)
    (by norm_num) s7c13pL_actual s7c13pW_actual s7c13p_hok s7c13p_hm s7c13p_hp s7c13p_hn s7c13p_ha
        s7c13p_ht

/-- The record gforest:S7c13+ as the wrapper hypothesis `SeventhCellIdentPos 13 6 _`. -/
theorem s7c13p_cell : SeventhCellIdentPos 13 6 s7c13pG := by
  unfold SeventhCellIdentPos
  rw [show seventhCellIdent 13 = s7c13pH from rfl]
  exact s7c13p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
