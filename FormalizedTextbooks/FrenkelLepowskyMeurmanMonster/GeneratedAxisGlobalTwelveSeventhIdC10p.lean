/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c10+ (gforest:S7c10+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c10+. -/
theorem s7c10p_ident : sExtra (rhoLocal (identWordLocal s7c10pH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c10pG) (generatedAxisGlobalTwelveRepresentative 6) := by
  exact ident_forward_selfM 6 6 _ _ s7c10pL s7c10pW (ofList_ok s7c10pHT s7c10pHT_labels)
    (ofList_ok s7c10pGT s7c10pGT_labels) s7c10pL_tenN s7c10pW_tenN s7c10pHXN_bnd s7c10pGXN_bnd (by
        norm_num)
    (by norm_num)
    (by norm_num) s7c10pL_actual s7c10pW_actual s7c10p_hok s7c10p_hm s7c10p_hp s7c10p_hn s7c10p_ha
        s7c10p_ht

/-- The record gforest:S7c10+ as the wrapper hypothesis `SeventhCellIdentPos 10 6 _`. -/
theorem s7c10p_cell : SeventhCellIdentPos 10 6 s7c10pG := by
  unfold SeventhCellIdentPos
  rw [show seventhCellIdent 10 = s7c10pH from rfl]
  exact s7c10p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
