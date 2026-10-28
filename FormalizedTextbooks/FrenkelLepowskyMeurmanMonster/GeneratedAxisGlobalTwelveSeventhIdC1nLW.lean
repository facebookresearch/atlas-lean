/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1nChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC1nChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP

/-! # Representations of both sides of the identification Seventh cell record S7c1-
(gforest:S7c1-, e = -1)

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
def s7c1nHP : List TPlan := [.letter (.xi), .letter (.xi), .letter (.mono (0, false))]

/-- The plan expands to the source word. -/
theorem s7c1nHP_word : planWord s7c1nHP = s7c1nH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s7c1nHP_ok : planOk s7c1nHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s7c1nHX : List SVec := tensorPlanF 64 s7c1nHP (srcSeventhX0F 64)

/-- The representation of the source image. -/
def s7c1nL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c1nH, ShortData.ofList s7c1nHT, 1 / srcSeventhD0,
    tensorRat 64 s7c1nHX ((tensorWordDenAll s7c1nH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c1nL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c1nH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c1nL.real := by
  have hT := (tensorPlanF_actual s7c1nHP s7c1nHP_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [s7c1nHP_word, s7c1nH_growth]; norm_num) srcSeventhD0).2
  rw [s7c1nHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 64) s7c1nHW s7c1nH_check s7c1nHD s7c1nHD_ok
      s7c1nHD_cols
    s7c1nHD_rows s7c1nHT s7c1nHT_check _ hT _ (seventhSrcGF_rep (w := 64) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c1nGP : List TPlan := [.letter (.qel (qmElt (9781912, false))),
    .letter (.sign 128 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (0, false), (1, false), (0, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (0, true), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, true), (0, false), (1, true),
        (0, false), (0, false), (0, false), (1, true), (0, true), (0, true), (1, true),
        (0, false), (0, false), (1, true), (0, false), (0, false), (1, true), (0, true),
        (1, true), (0, false), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, false), (1, false), (0, false), (1, false)]
      [.trans 3 1, .trans 4 9, .trans 0 3, .trans 5 4, .trans 0 11, .trans 8 5, .trans 4 8,
        .trans 9 4, .trans 8 6, .trans 2 0, .trans 3 0, .trans 1 2, .trans 10 2,
        .trans 2 11, .trans 3 2, .trans 6 4, .trans 6 8, .trans 9 7, .trans 7 9,
        .trans 8 7, .trans 8 9, .trans 9 4, .trans 9 5, .trans 9 6, .trans 9 8],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (1, true)]
      [.trans 1 0, .trans 0 1, .trans 0 2, .trans 0 3, .trans 0 5, .trans 0 7, .trans 0 9,
        .trans 0 10, .trans 0 11, .trans 5 1, .trans 1 0, .trans 1 5, .trans 1 7,
        .trans 1 8, .trans 1 10, .trans 1 11, .trans 2 3, .trans 2 4, .trans 2 5,
        .trans 2 11, .trans 4 3, .trans 3 0, .trans 3 2, .trans 3 4, .trans 3 6,
        .trans 3 9, .trans 3 10, .trans 3 11, .trans 9 4, .trans 4 0, .trans 4 9,
        .trans 4 10, .trans 4 11, .trans 6 5, .trans 5 1, .trans 5 3, .trans 5 4,
        .trans 5 6, .trans 5 8, .trans 8 6, .trans 6 0, .trans 6 1, .trans 6 2,
        .trans 6 3, .trans 6 8, .trans 6 10, .trans 6 11, .trans 7 0, .trans 7 1,
        .trans 7 3, .trans 7 4, .trans 7 10, .trans 7 11, .trans 8 0, .trans 8 1,
        .trans 8 2, .trans 8 4, .trans 8 6, .trans 8 10, .trans 9 3, .trans 9 4,
        .trans 9 5, .trans 9 6, .trans 9 8, .trans 9 10, .trans 9 11, .trans 10 1,
        .trans 10 4, .trans 10 6]]

/-- The plan expands to the target word. -/
theorem s7c1nGP_word : planWord s7c1nGP = s7c1nG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s7c1nGP_ok : planOk s7c1nGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s7c1nGX : List SVec := tensorPlanF 64 s7c1nGP (srcSeventhX0F 64)

/-- The representation of the target image. -/
def s7c1nW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c1nG, ShortData.ofList s7c1nGT, 1 / srcSeventhD0,
    tensorRat 64 s7c1nGX ((tensorWordDenAll s7c1nG : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the target image. -/
theorem s7c1nW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c1nG)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c1nW.real := by
  have hT := (tensorPlanF_actual s7c1nGP s7c1nGP_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [s7c1nGP_word, s7c1nG_growth]; norm_num) srcSeventhD0).2
  rw [s7c1nGP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 64) s7c1nGW s7c1nG_check s7c1nGD s7c1nGD_ok
      s7c1nGD_cols
    s7c1nGD_rows s7c1nGT s7c1nGT_check _ hT _ (seventhSrcGF_rep (w := 64) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
