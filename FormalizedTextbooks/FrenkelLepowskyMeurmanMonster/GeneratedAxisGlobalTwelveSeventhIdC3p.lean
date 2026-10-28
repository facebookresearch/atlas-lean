/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c3+ (gforest:S7c3+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c3+. -/
theorem s7c3p_ident : sExtra (rhoLocal (identWordLocal s7c3pH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c3pG) (generatedAxisGlobalTwelveRepresentative 4) := by
  exact ident_forward_selfM 6 4 _ _ s7c3pL s7c3pW (ofList_ok s7c3pHT s7c3pHT_labels)
    (ofList_ok s7c3pGT s7c3pGT_labels) s7c3pL_tenN s7c3pW_tenN s7c3pHXN_bnd s7c3pGXN_bnd (by
        norm_num)
    (by norm_num)
    (by norm_num) s7c3pL_actual s7c3pW_actual s7c3p_hok s7c3p_hm s7c3p_hp s7c3p_hn s7c3p_ha s7c3p_ht

/-- The record gforest:S7c3+ as the wrapper hypothesis `SeventhCellIdentPos 3 4 _`. -/
theorem s7c3p_cell : SeventhCellIdentPos 3 4 s7c3pG := by
  unfold SeventhCellIdentPos
  rw [show seventhCellIdent 3 = s7c3pH from rfl]
  exact s7c3p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
