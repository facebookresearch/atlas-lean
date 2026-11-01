/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC20nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC20nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC20nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC20nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdent

/-! # The identification Seventh cell record S7c20- (gforest:S7c20-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification of record gforest:S7c20-. -/
theorem s7c20n_ident : sExtra.symm (rhoLocal (identWordLocal s7c20nH)
    (generatedAxisGlobalTwelveRepresentative 6)) =
      rhoLocal (identWordLocal s7c20nG) (generatedAxisGlobalTwelveRepresentative 6) := by
  have hX := (tensorPlanF_actual s7c20nHP s7c20nHP_ok (srcSeventhX0F_bnd (w := 80) (by norm_num))
    (by rw [s7c20nHP_word, s7c20nH_growth]; norm_num) srcSeventhD0).1
  have hY := (tensorPlanF_actual s7c20nGP s7c20nGP_ok (srcSeventhX0F_bnd (w := 80) (by norm_num))
    (by rw [s7c20nGP_word, s7c20nG_growth]; norm_num) srcSeventhD0).1
  exact ident_inverse_selfM 6 6 _ _ s7c20nL s7c20nW (ofList_ok s7c20nHT s7c20nHT_labels)
    (ofList_ok s7c20nGT s7c20nGT_labels) rfl rfl (tbnd_tight 80 29 _ s7c20nHX hX (by norm_num)
        s7c20n_xlt)
    (tbnd_tight 80 31 _ s7c20nGX hY (by norm_num) s7c20n_ylt) (by norm_num) (by norm_num)
    (by norm_num) s7c20nL_actual s7c20nW_actual s7c20n_hok s7c20n_hm s7c20n_hp s7c20n_hn s7c20n_ha
        s7c20n_ht

/-- The record gforest:S7c20- as the wrapper hypothesis `SeventhCellIdentNeg 20 6 _`. -/
theorem s7c20n_cell : SeventhCellIdentNeg 20 6 s7c20nG := by
  unfold SeventhCellIdentNeg
  rw [show seventhCellIdent 20 = s7c20nH from rfl]
  exact s7c20n_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
