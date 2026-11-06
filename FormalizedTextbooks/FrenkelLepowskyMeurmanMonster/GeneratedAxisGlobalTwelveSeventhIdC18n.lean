/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC18nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC18nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC18nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC18nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c18- (gforest:S7c18-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c18-. -/
theorem s7c18n_ident : sExtra.symm (rhoLocal (identWordLocal s7c18nH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c18nG) (generatedAxisGlobalTwelveRepresentative 6) := by
  have hX := (tensorPlanF_actual s7c18nHP rfl (srcSeventhX0F_bnd (w := 72) (by norm_num))
    (by rw [s7c18nHP_word, s7c18nH_growth]; norm_num) srcSeventhD0).1
  have hY := (tensorPlanF_actual s7c18nGP rfl (srcSeventhX0F_bnd (w := 72) (by norm_num))
    (by rw [s7c18nGP_word, s7c18nG_growth]; norm_num) srcSeventhD0).1
  exact ident_inverse_selfM 6 6 _ _ s7c18nL s7c18nW (ofList_ok s7c18nHT s7c18nHT_labels)
    (ofList_ok s7c18nGT s7c18nGT_labels) rfl rfl (tbnd_tight 72 28 _ s7c18nHX hX (by norm_num)
        s7c18n_xlt)
    (tbnd_tight 72 28 _ s7c18nGX hY (by norm_num) s7c18n_ylt) (by norm_num) (by norm_num)
    (by norm_num) s7c18nL_actual s7c18nW_actual s7c18n_hok s7c18n_hm s7c18n_hp s7c18n_hn s7c18n_ha
        s7c18n_ht

/-- The record gforest:S7c18- as the wrapper hypothesis `SeventhCellIdentNeg 18 6 _`. -/
theorem s7c18n_cell : SeventhCellIdentNeg 18 6 s7c18nG := by
  unfold SeventhCellIdentNeg
  rw [show seventhCellIdent 18 = s7c18nH from rfl]
  exact s7c18n_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
