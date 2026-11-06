/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdent

/-! # The identification Sixth cell record S6c6+ (gforest:S6c6+, e = 1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_forward_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S6c6+. -/
theorem s6c6p_ident : sExtra (rhoLocal (identWordLocal s6c6pH)
    (generatedAxisGlobalTwelveRepresentative 5)) =
      rhoLocal (identWordLocal s6c6pG) (generatedAxisGlobalTwelveRepresentative 5) := by
  exact ident_forward_selfM 5 5 _ _ s6c6pL s6c6pW (ofList_ok s6c6pHT s6c6pHT_labels)
    (ofList_ok s6c6pGT s6c6pGT_labels) s6c6pL_tenN s6c6pW_tenN s6c6pHXN_bnd s6c6pGXN_bnd (by
        norm_num)
    (by norm_num)
    (by norm_num) s6c6pL_actual s6c6pW_actual s6c6p_hok s6c6p_hm s6c6p_hp s6c6p_hn s6c6p_ha s6c6p_ht

/-- The record gforest:S6c6+ as the wrapper hypothesis `SixthCellIdentPos 6 5 _`. -/
theorem s6c6p_cell : SixthCellIdentPos 6 5 s6c6pG := by
  unfold SixthCellIdentPos
  rw [show sixthCellIdent 6 = s6c6pH from rfl]
  exact s6c6p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
