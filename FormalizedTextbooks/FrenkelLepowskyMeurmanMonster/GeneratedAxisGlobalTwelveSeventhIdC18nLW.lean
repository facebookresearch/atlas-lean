/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC18nChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC18nChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP

/-! # Representations of both sides of the identification Seventh cell record S7c18-
(gforest:S7c18-, e = -1)

The two images are computed from the source vector (matrix block by the spatial alphabet, short
block by the
checked transports, tensor block by fast tensor plans) and bound to the genuine coordinates of the
local images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor plan of the source word (one step per letter, fast Xi letter). -/
def s7c18nHP : List TPlan := [.letter (.xi), .letter (.xi), .letter (.mono (0, false)), .letter
    (.mono (0, false))]

/-- The plan expands to the source word. -/
theorem s7c18nHP_word : planWord s7c18nHP = s7c18nH := rfl

/-- The packed tensor of the source image. -/
def s7c18nHX : List SVec := tensorPlanF 72 s7c18nHP (srcSeventhX0F 72)

/-- The representation of the source image. -/
def s7c18nL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c18nH, ShortData.ofList s7c18nHT, 1 / srcSeventhD0,
    tensorRat 72 s7c18nHX ((tensorWordDenAll s7c18nH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c18nL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c18nH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c18nL.real := by
  have hT := (tensorPlanF_actual s7c18nHP rfl (srcSeventhX0F_bnd (w := 72) (by norm_num))
    (by rw [s7c18nHP_word, s7c18nH_growth]; norm_num) srcSeventhD0).2
  rw [s7c18nHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 72) s7c18nHW s7c18nH_check s7c18nHD s7c18nHD_ok
      s7c18nHD_cols
    s7c18nHD_rows s7c18nHT s7c18nHT_check _ hT _ (seventhSrcGF_rep (w := 72) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c18nGP : List TPlan := [.letter (.qel (qmElt (10186752, false))), .letter (.xi), .letter
    (.xi), .letter (.mono (0, false)), .letter (.mono (0, false))]

/-- The plan expands to the target word. -/
theorem s7c18nGP_word : planWord s7c18nGP = s7c18nG := rfl

/-- The packed tensor of the target image. -/
def s7c18nGX : List SVec := tensorPlanF 72 s7c18nGP (srcSeventhX0F 72)

/-- The representation of the target image. -/
def s7c18nW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c18nG, ShortData.ofList s7c18nGT, 1 / srcSeventhD0,
    tensorRat 72 s7c18nGX ((tensorWordDenAll s7c18nG : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the target image. -/
theorem s7c18nW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c18nG)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c18nW.real := by
  have hT := (tensorPlanF_actual s7c18nGP rfl (srcSeventhX0F_bnd (w := 72) (by norm_num))
    (by rw [s7c18nGP_word, s7c18nG_growth]; norm_num) srcSeventhD0).2
  rw [s7c18nGP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 72) s7c18nGW s7c18nG_check s7c18nGD s7c18nGD_ok
      s7c18nGD_cols
    s7c18nGD_rows s7c18nGT s7c18nGT_check _ hT _ (seventhSrcGF_rep (w := 72) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
