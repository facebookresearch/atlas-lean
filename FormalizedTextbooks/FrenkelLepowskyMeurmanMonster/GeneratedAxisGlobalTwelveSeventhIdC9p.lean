/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC9pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC9pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC9pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC9pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c9+ (gforest:S7c9+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c9+. -/
theorem s7c9p_ident : sExtra (rhoLocal (identWordLocal s7c9pH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c9pG) (generatedAxisGlobalTwelveRepresentative 10) := by
  exact ident_forward_selfM 6 10 _ _ s7c9pL s7c9pW (ofList_ok s7c9pHT s7c9pHT_labels)
    (ofList_ok s7c9pGT s7c9pGT_labels) s7c9pL_tenN s7c9pW_tenN s7c9pHXN_bnd s7c9pGXN_bnd (by
        norm_num)
    (by norm_num)
    (by norm_num) s7c9pL_actual s7c9pW_actual s7c9p_hok s7c9p_hm s7c9p_hp s7c9p_hn s7c9p_ha s7c9p_ht

/-- The record gforest:S7c9+ as the wrapper hypothesis `SeventhCellIdentPos 9 10 _`. -/
theorem s7c9p_cell : SeventhCellIdentPos 9 10 s7c9pG := by
  unfold SeventhCellIdentPos
  rw [show seventhCellIdent 9 = s7c9pH from rfl]
  exact s7c9p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
