/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10nChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight

/-! # Representations of both sides of the identification Seventh cell record S7c10-
(gforest:S7c10-, e = -1)

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
def s7c10nHP : List TPlan := [.letter (.xi),
    .run
      [(0, true), (0, true), (1, true)]
      [.trans 5 4, .trans 7 1, .trans 8 3, .trans 3 5, .trans 9 10, .trans 6 7, .trans 1 9,
        .trans 9 0, .trans 10 8, .trans 8 6, .trans 6 2, .trans 7 4, .trans 5 11,
        .trans 7 11, .trans 9 11, .trans 0 4, .trans 4 9, .trans 9 3, .trans 9 2,
        .trans 9 1, .trans 2 7, .trans 9 11, .trans 5 7, .trans 1 7, .trans 7 2,
        .trans 7 10, .trans 0 3, .trans 3 8, .trans 3 10, .trans 8 3, .trans 8 6,
        .trans 6 8, .trans 6 5, .trans 5 0, .trans 0 4, .trans 4 2, .trans 2 6,
        .trans 2 8, .trans 8 10, .trans 10 1, .trans 1 6, .trans 6 5, .trans 1 3],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

/-- The plan expands to the source word. -/
theorem s7c10nHP_word : planWord s7c10nHP = s7c10nH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s7c10nHP_ok : planOk s7c10nHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s7c10nHX : List SVec := tensorPlanF 64 s7c10nHP (srcSeventhX0F 64)

/-- The representation of the source image. -/
def s7c10nL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c10nH, ShortData.ofList s7c10nHT, 1 / srcSeventhD0,
    tensorRat 64 s7c10nHX ((tensorWordDenAll s7c10nH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c10nL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c10nH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c10nL.real := by
  have hT := (tensorPlanF_actual s7c10nHP s7c10nHP_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [s7c10nHP_word, s7c10nH_growth]; norm_num) srcSeventhD0).2
  rw [s7c10nHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 64) s7c10nHW s7c10nH_check s7c10nHD s7c10nHD_ok
      s7c10nHD_cols
    s7c10nHD_rows s7c10nHT s7c10nHT_check _ hT _ (seventhSrcGF_rep (w := 64) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c10nGP : List TPlan := [.letter (.qel (qmElt (7090055, true))),
    .letter (.sign 1472 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (0, false), (1, false), (0, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (0, true), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, true), (0, false), (1, true),
        (0, false), (0, false), (0, false), (1, true), (0, true), (0, true), (1, true),
        (0, false), (0, false), (1, true), (0, false), (0, false), (1, true), (0, true),
        (1, true), (0, false), (0, false), (0, false), (1, false), (0, true), (0, true),
        (1, false), (0, false), (0, false), (1, false), (0, false), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (1, false),
        (0, true), (0, true), (1, false), (0, false)]
      [.trans 0 2, .trans 0 1, .trans 10 0, .trans 7 5, .trans 4 3, .trans 6 4, .trans 6 8,
        .trans 0 6, .trans 8 3, .trans 10 8, .trans 9 10, .trans 5 7, .trans 7 4,
        .trans 4 7, .trans 9 6, .trans 9 4, .trans 8 0, .trans 0 8, .trans 5 3,
        .trans 3 1, .trans 0 3, .trans 1 0, .trans 1 2, .trans 1 3, .trans 2 6,
        .trans 3 6, .trans 8 5, .trans 5 8, .trans 6 9, .trans 7 0, .trans 7 3,
        .trans 7 5, .trans 7 6, .trans 7 9, .trans 10 8, .trans 8 10, .trans 9 1,
        .trans 9 2, .trans 9 5, .trans 9 6, .trans 9 7, .trans 10 5],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (0, true)]
      [.trans 1 2, .trans 8 3, .trans 10 5, .trans 8 9, .trans 2 8, .trans 4 7, .trans 7 0,
        .trans 4 8, .trans 8 3, .trans 5 9, .trans 5 4, .trans 10 6, .trans 6 4,
        .trans 6 8, .trans 5 10, .trans 10 1, .trans 0 4, .trans 3 2, .trans 2 11,
        .trans 7 6, .trans 6 7, .trans 6 9, .trans 0 2, .trans 9 11, .trans 4 6,
        .trans 7 10, .trans 10 11, .trans 9 2, .trans 6 1, .trans 1 11],
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11]]

/-- The plan expands to the target word. -/
theorem s7c10nGP_word : planWord s7c10nGP = s7c10nG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s7c10nGP_ok : planOk s7c10nGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s7c10nGX : List SVec := tensorPlanF 64 s7c10nGP (rootEightSrcXL 64)

/-- The representation of the target image. -/
def s7c10nW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet s7c10nG, ShortData.ofList s7c10nGT, 1 / 128,
    tensorRat 64 s7c10nGX ((tensorWordDenAll s7c10nG : ℚ) * 32)⟩

/-- The coordinates of the target image. -/
theorem s7c10nW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c10nG)
    (generatedAxisGlobalTwelveRepresentative 9)) = s7c10nW.real := by
  have hT := (tensorPlanF_actual s7c10nGP s7c10nGP_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [s7c10nGP_word, s7c10nG_growth]; norm_num) 32).2
  rw [s7c10nGP_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) s7c10nGW s7c10nG_check s7c10nGD s7c10nGD_ok
      s7c10nGD_cols
    s7c10nGD_rows s7c10nGT s7c10nGT_check _ hT _ (rootEightSrcL_rep (w := 64) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
