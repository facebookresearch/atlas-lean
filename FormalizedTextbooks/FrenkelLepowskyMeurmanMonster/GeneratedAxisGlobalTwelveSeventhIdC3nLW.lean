/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3nChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3nChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP

/-! # Representations of both sides of the identification Seventh cell record S7c3-
(gforest:S7c3-, e = -1)

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
def s7c3nHP : List TPlan := [.letter (.xi), .letter (.xi), .letter (.mono (1, true))]

/-- The plan expands to the source word. -/
theorem s7c3nHP_word : planWord s7c3nHP = s7c3nH := rfl

/-- The packed tensor of the source image. -/
def s7c3nHX : List SVec := tensorPlanF 80 s7c3nHP (srcSeventhX0F 80)

/-- The representation of the source image. -/
def s7c3nL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c3nH, ShortData.ofList s7c3nHT, 1 / srcSeventhD0,
    tensorRat 80 s7c3nHX ((tensorWordDenAll s7c3nH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c3nL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c3nH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c3nL.real := by
  have hT := (tensorPlanF_actual s7c3nHP rfl (srcSeventhX0F_bnd (w := 80) (by norm_num))
    (by rw [s7c3nHP_word, s7c3nH_growth]; norm_num) srcSeventhD0).2
  rw [s7c3nHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 80) s7c3nHW s7c3nH_check s7c3nHD s7c3nHD_ok
      s7c3nHD_cols
    s7c3nHD_rows s7c3nHT s7c3nHT_check _ hT _ (seventhSrcGF_rep (w := 80) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c3nGP : List TPlan := [.letter (.qel (qmElt (12611584, true))), .letter (.sign 1016 0),
    .letter (.xi), .letter (.xi), .letter (.mono (1, true))]

/-- The plan expands to the target word. -/
theorem s7c3nGP_word : planWord s7c3nGP = s7c3nG := rfl

/-- The packed tensor of the target image. -/
def s7c3nGX : List SVec := tensorPlanF 80 s7c3nGP (srcSeventhX0F 80)

/-- The representation of the target image. -/
def s7c3nW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c3nG, ShortData.ofList s7c3nGT, 1 / srcSeventhD0,
    tensorRat 80 s7c3nGX ((tensorWordDenAll s7c3nG : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the target image. -/
theorem s7c3nW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c3nG)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c3nW.real := by
  have hT := (tensorPlanF_actual s7c3nGP rfl (srcSeventhX0F_bnd (w := 80) (by norm_num))
    (by rw [s7c3nGP_word, s7c3nG_growth]; norm_num) srcSeventhD0).2
  rw [s7c3nGP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 80) s7c3nGW s7c3nG_check s7c3nGD s7c3nGD_ok
      s7c3nGD_cols
    s7c3nGD_rows s7c3nGT s7c3nGT_check _ hT _ (seventhSrcGF_rep (w := 80) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
