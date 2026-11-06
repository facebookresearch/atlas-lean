/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC16pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC16pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC16pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC16pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c16+ (gforest:S7c16+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c16+. -/
theorem s7c16p_ident : sExtra (rhoLocal (identWordLocal s7c16pH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c16pG) (generatedAxisGlobalTwelveRepresentative 9) := by
  exact ident_forward_selfM 6 9 _ _ s7c16pL s7c16pW (ofList_ok s7c16pHT s7c16pHT_labels)
    (ofList_ok s7c16pGT s7c16pGT_labels) s7c16pL_tenN s7c16pW_tenN s7c16pHXN_bnd s7c16pGXN_bnd (by
        norm_num)
    (by norm_num)
    (by norm_num) s7c16pL_actual s7c16pW_actual s7c16p_hok s7c16p_hm s7c16p_hp s7c16p_hn s7c16p_ha
        s7c16p_ht

/-- The record gforest:S7c16+ as the wrapper hypothesis `SeventhCellIdentPos 16 9 _`. -/
theorem s7c16p_cell : SeventhCellIdentPos 16 9 s7c16pG := by
  unfold SeventhCellIdentPos
  rw [show seventhCellIdent 16 = s7c16pH from rfl]
  exact s7c16p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
