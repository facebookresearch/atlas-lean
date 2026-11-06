/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC20nChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC20nChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP

/-! # Representations of both sides of the identification Seventh cell record S7c20-
(gforest:S7c20-, e = -1)

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
def s7c20nHP : List TPlan := [.letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, true)]
      [.trans 5 0, .trans 1 5, .trans 1 3, .trans 3 4, .trans 3 11, .trans 10 1, .trans 4 9,
        .trans 7 3, .trans 4 7, .trans 3 10, .trans 5 6, .trans 5 11, .trans 10 2,
        .trans 7 5, .trans 0 1, .trans 5 1, .trans 1 5, .trans 3 9, .trans 8 9,
        .trans 5 11, .trans 1 6, .trans 9 3, .trans 9 6, .trans 6 7, .trans 1 0,
        .trans 5 8, .trans 9 2, .trans 7 4, .trans 2 10, .trans 10 8, .trans 8 3,
        .trans 0 8, .trans 4 0, .trans 4 8, .trans 8 0, .trans 8 4]]

/-- The plan expands to the source word. -/
theorem s7c20nHP_word : planWord s7c20nHP = s7c20nH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s7c20nHP_ok : planOk s7c20nHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s7c20nHX : List SVec := tensorPlanF 80 s7c20nHP (srcSeventhX0F 80)

/-- The representation of the source image. -/
def s7c20nL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c20nH, ShortData.ofList s7c20nHT, 1 / srcSeventhD0,
    tensorRat 80 s7c20nHX ((tensorWordDenAll s7c20nH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c20nL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c20nH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c20nL.real := by
  have hT := (tensorPlanF_actual s7c20nHP s7c20nHP_ok (srcSeventhX0F_bnd (w := 80) (by norm_num))
    (by rw [s7c20nHP_word, s7c20nH_growth]; norm_num) srcSeventhD0).2
  rw [s7c20nHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 80) s7c20nHW s7c20nH_check s7c20nHD s7c20nHD_ok
      s7c20nHD_cols
    s7c20nHD_rows s7c20nHT s7c20nHT_check _ hT _ (seventhSrcGF_rep (w := 80) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c20nGP : List TPlan := [.letter (.qel (qmElt (8388608, false))),
    .letter (.sign 144 0),
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, true)]
      [.trans 5 0, .trans 1 5, .trans 1 3, .trans 3 4, .trans 3 11, .trans 10 1, .trans 4 9,
        .trans 7 3, .trans 4 7, .trans 3 10, .trans 5 6, .trans 5 11, .trans 10 2,
        .trans 7 5, .trans 0 1, .trans 5 1, .trans 1 5, .trans 3 9, .trans 8 9,
        .trans 5 11, .trans 1 6, .trans 9 3, .trans 9 6, .trans 6 7, .trans 1 0,
        .trans 5 8, .trans 9 2, .trans 7 4, .trans 2 10, .trans 10 8, .trans 8 3,
        .trans 0 8, .trans 4 0, .trans 4 8, .trans 8 0, .trans 8 4]]

/-- The plan expands to the target word. -/
theorem s7c20nGP_word : planWord s7c20nGP = s7c20nG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s7c20nGP_ok : planOk s7c20nGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s7c20nGX : List SVec := tensorPlanF 80 s7c20nGP (srcSeventhX0F 80)

/-- The representation of the target image. -/
def s7c20nW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c20nG, ShortData.ofList s7c20nGT, 1 / srcSeventhD0,
    tensorRat 80 s7c20nGX ((tensorWordDenAll s7c20nG : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the target image. -/
theorem s7c20nW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c20nG)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c20nW.real := by
  have hT := (tensorPlanF_actual s7c20nGP s7c20nGP_ok (srcSeventhX0F_bnd (w := 80) (by norm_num))
    (by rw [s7c20nGP_word, s7c20nG_growth]; norm_num) srcSeventhD0).2
  rw [s7c20nGP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 80) s7c20nGW s7c20nG_check s7c20nGD s7c20nGD_ok
      s7c20nGD_cols
    s7c20nGD_rows s7c20nGT s7c20nGT_check _ hT _ (seventhSrcGF_rep (w := 80) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
