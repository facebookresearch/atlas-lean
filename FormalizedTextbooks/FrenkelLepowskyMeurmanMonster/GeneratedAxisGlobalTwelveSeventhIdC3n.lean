/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c3- (gforest:S7c3-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c3-. -/
theorem s7c3n_ident : sExtra.symm (rhoLocal (identWordLocal s7c3nH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c3nG) (generatedAxisGlobalTwelveRepresentative 6) := by
  have hX := (tensorPlanF_actual s7c3nHP rfl (srcSeventhX0F_bnd (w := 80) (by norm_num))
    (by rw [s7c3nHP_word, s7c3nH_growth]; norm_num) srcSeventhD0).1
  have hY := (tensorPlanF_actual s7c3nGP rfl (srcSeventhX0F_bnd (w := 80) (by norm_num))
    (by rw [s7c3nGP_word, s7c3nG_growth]; norm_num) srcSeventhD0).1
  exact ident_inverse_selfM 6 6 _ _ s7c3nL s7c3nW (ofList_ok s7c3nHT s7c3nHT_labels)
    (ofList_ok s7c3nGT s7c3nGT_labels) rfl rfl (tbnd_tight 80 29 _ s7c3nHX hX (by norm_num)
        s7c3n_xlt)
    (tbnd_tight 80 31 _ s7c3nGX hY (by norm_num) s7c3n_ylt) (by norm_num) (by norm_num)
    (by norm_num) s7c3nL_actual s7c3nW_actual s7c3n_hok s7c3n_hm s7c3n_hp s7c3n_hn s7c3n_ha s7c3n_ht

/-- The record gforest:S7c3- as the wrapper hypothesis `SeventhCellIdentNeg 3 6 _`. -/
theorem s7c3n_cell : SeventhCellIdentNeg 3 6 s7c3nG := by
  unfold SeventhCellIdentNeg
  rw [show seventhCellIdent 3 = s7c3nH from rfl]
  exact s7c3n_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
