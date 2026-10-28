/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC1nChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC1nChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP

/-! # Representations of both sides of the identification Sixth cell record S6c1- (gforest:S6c1-,
e = -1)

The two images are computed from the source vector (matrix block by the spatial alphabet, short
block by the
checked transports, tensor block by fast tensor plans) and bound to the genuine coordinates of the
local images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor plan of the source word (one step per letter, fast Xi letter). -/
def s6c1nHP : List TPlan := [.letter (.xi), .letter (.xi), .letter (.mono (0, false))]

/-- The plan expands to the source word. -/
theorem s6c1nHP_word : planWord s6c1nHP = s6c1nH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s6c1nHP_ok : planOk s6c1nHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s6c1nHX : List SVec := tensorPlanF 64 s6c1nHP (sixthSXF 64)

/-- The representation of the source image. -/
def s6c1nL : IdentVec :=
  ⟨sixthSrcMat.act identSpatialAlphabet s6c1nH, ShortData.ofList s6c1nHT, 1 / 32,
    tensorRat 64 s6c1nHX ((tensorWordDenAll s6c1nH : ℚ) * 32)⟩

/-- The coordinates of the source image. -/
theorem s6c1nL_actual : griessConwayEncode (rhoLocal (identWordLocal s6c1nH)
    (generatedAxisGlobalTwelveRepresentative 5)) = s6c1nL.real := by
  have hT := (tensorPlanF_actual s6c1nHP s6c1nHP_ok (sixthSXF_bndF (w := 64) (by norm_num))
    (by rw [s6c1nHP_word, s6c1nH_growth]; norm_num) 32).2
  rw [s6c1nHP_word] at hT
  exact IdentVec.word_actual (sixthSrcVecF 64) s6c1nHW s6c1nH_check s6c1nHD s6c1nHD_ok s6c1nHD_cols
    s6c1nHD_rows s6c1nHT s6c1nHT_check _ hT _ (sixthSrcF_rep (w := 64) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s6c1nGP : List TPlan := [.letter (.qel (qmElt (12694168, true))),
    .letter (.sign 240 0),
    .run
      [(0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false),
        (1, false), (0, true), (0, true), (1, false), (0, true), (1, false), (0, false),
        (1, false), (0, false), (0, false), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, true), (0, true), (0, true), (1, true), (0, false),
        (1, true), (0, false), (0, false), (0, false), (1, true), (0, true), (1, true),
        (0, true), (0, true), (0, true), (1, true), (0, false), (1, true), (0, true),
        (0, true), (1, true), (0, false), (0, false), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (1, false),
        (0, false)]
      [.trans 5 4, .trans 4 0, .trans 0 3, .trans 5 1, .trans 0 11, .trans 8 1, .trans 7 4,
        .trans 8 4, .trans 4 3, .trans 3 0, .trans 3 2, .trans 10 5, .trans 7 9,
        .trans 9 7, .trans 6 8, .trans 8 6, .trans 8 5, .trans 10 0, .trans 7 5,
        .trans 5 9, .trans 9 2, .trans 5 4, .trans 4 1, .trans 4 8, .trans 8 2,
        .trans 2 11, .trans 2 1, .trans 1 0, .trans 0 3, .trans 0 11],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true)]
      [.trans 3 11, .trans 7 6, .trans 4 5, .trans 11 2, .trans 10 3, .trans 4 1, .trans 1 8,
        .trans 9 7, .trans 6 10, .trans 10 9, .trans 3 7, .trans 6 2, .trans 10 11,
        .trans 7 4, .trans 11 4, .trans 10 8, .trans 5 1, .trans 1 9, .trans 4 2,
        .trans 2 3, .trans 9 11, .trans 8 0, .trans 2 0, .trans 5 6, .trans 7 9,
        .trans 9 8, .trans 8 3, .trans 8 11, .trans 8 10, .trans 8 7, .trans 0 5,
        .trans 1 0, .trans 1 5, .trans 3 4, .trans 4 2, .trans 4 7, .trans 4 9,
        .trans 5 6, .trans 5 11, .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 3,
        .trans 6 4, .trans 6 7, .trans 6 9, .trans 9 10, .trans 11 2, .trans 11 4,
        .trans 11 7, .trans 11 9, .trans 11 10]]

/-- The plan expands to the target word. -/
theorem s6c1nGP_word : planWord s6c1nGP = s6c1nG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s6c1nGP_ok : planOk s6c1nGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s6c1nGX : List SVec := tensorPlanF 64 s6c1nGP (srcSeventhX0F 64)

/-- The representation of the target image. -/
def s6c1nW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s6c1nG, ShortData.ofList s6c1nGT, 1 / srcSeventhD0,
    tensorRat 64 s6c1nGX ((tensorWordDenAll s6c1nG : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the target image. -/
theorem s6c1nW_actual : griessConwayEncode (rhoLocal (identWordLocal s6c1nG)
    (generatedAxisGlobalTwelveRepresentative 6)) = s6c1nW.real := by
  have hT := (tensorPlanF_actual s6c1nGP s6c1nGP_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [s6c1nGP_word, s6c1nG_growth]; norm_num) srcSeventhD0).2
  rw [s6c1nGP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 64) s6c1nGW s6c1nG_check s6c1nGD s6c1nGD_ok
      s6c1nGD_cols
    s6c1nGD_rows s6c1nGT s6c1nGT_check _ hT _ (seventhSrcGF_rep (w := 64) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
