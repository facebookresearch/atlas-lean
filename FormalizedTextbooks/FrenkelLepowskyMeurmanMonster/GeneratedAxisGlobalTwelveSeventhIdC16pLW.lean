/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC16pChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC16pChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight

/-! # Representations of both sides of the identification Seventh cell record S7c16+
(gforest:S7c16+, e = 1)

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
def s7c16pHP : List TPlan := [.letter (.xi), .letter (.xi), .letter (.mono (1, true)), .letter
    (.xi), .letter (.xi), .letter (.mono (0, true))]

/-- The plan expands to the source word. -/
theorem s7c16pHP_word : planWord s7c16pHP = s7c16pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s7c16pHP_ok : planOk s7c16pHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s7c16pHX : List SVec := tensorPlanF 64 s7c16pHP (srcSeventhX0F 64)

/-- The representation of the source image. -/
def s7c16pL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c16pH, ShortData.ofList s7c16pHT, 1 / srcSeventhD0,
    tensorRat 64 s7c16pHX ((tensorWordDenAll s7c16pH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c16pL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c16pH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c16pL.real := by
  have hT := (tensorPlanF_actual s7c16pHP s7c16pHP_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [s7c16pHP_word, s7c16pH_growth]; norm_num) srcSeventhD0).2
  rw [s7c16pHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 64) s7c16pHW s7c16pH_check s7c16pHD s7c16pHD_ok
      s7c16pHD_cols
    s7c16pHD_rows s7c16pHT s7c16pHT_check _ hT _ (seventhSrcGF_rep (w := 64) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c16pGP : List TPlan := [.letter (.qel (qmElt (304622, false))),
    .letter (.sign 1618 0),
    .run
      [(0, false), (0, false), (1, false), (0, true), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, false), (0, false), (1, false), (0, false),
        (1, false), (0, false), (0, false), (1, false), (0, false), (1, false),
        (0, false), (0, false), (1, false), (0, true), (0, true), (0, true), (1, false),
        (0, false), (0, false), (0, false), (1, true), (0, false), (1, true), (0, false),
        (0, false), (1, true), (0, true), (0, true), (1, true), (0, true), (0, true),
        (1, true), (0, false), (1, true), (0, true), (0, true), (1, true), (0, false),
        (0, false), (1, true), (0, true), (0, true), (0, true), (0, true), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, true), (0, true), (1, false),
        (0, true), (0, true), (1, false), (0, true), (0, true), (0, true), (1, false),
        (0, false), (1, false)]
      [.trans 0 4, .trans 0 5, .trans 0 7, .trans 0 8, .trans 2 1, .trans 1 2, .trans 1 4,
        .trans 1 5, .trans 1 7, .trans 1 8, .trans 3 2, .trans 2 3, .trans 2 7,
        .trans 2 8, .trans 3 1, .trans 3 2, .trans 3 4, .trans 3 5, .trans 3 7,
        .trans 3 8, .trans 4 0, .trans 4 1, .trans 4 5, .trans 5 0, .trans 5 3,
        .trans 8 6, .trans 6 0, .trans 6 3, .trans 6 4, .trans 6 8, .trans 9 7,
        .trans 7 2, .trans 7 3, .trans 7 5, .trans 7 6, .trans 7 9, .trans 7 10,
        .trans 9 8, .trans 8 0, .trans 8 2, .trans 8 4, .trans 8 5, .trans 8 6,
        .trans 8 7, .trans 8 9, .trans 8 10, .trans 9 1, .trans 9 2, .trans 9 3,
        .trans 9 4, .trans 9 7, .trans 9 8, .trans 10 2, .trans 10 4, .trans 10 5,
        .trans 10 8],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (1, true), (0, true)]
      [.trans 6 5, .trans 10 1, .trans 4 7, .trans 4 10, .trans 3 4, .trans 10 2, .trans 5 3,
        .trans 9 6, .trans 8 6, .trans 0 5, .trans 0 2, .trans 2 11, .trans 5 1,
        .trans 5 8, .trans 8 9, .trans 9 4, .trans 4 9, .trans 4 7, .trans 4 10,
        .trans 3 0, .trans 0 3, .trans 1 2, .trans 2 4, .trans 7 3, .trans 3 7,
        .trans 3 8, .trans 3 9, .trans 3 11, .trans 6 4, .trans 4 6, .trans 4 8,
        .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 10, .trans 7 0, .trans 10 4,
        .trans 10 8, .trans 10 11]]

/-- The plan expands to the target word. -/
theorem s7c16pGP_word : planWord s7c16pGP = s7c16pG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s7c16pGP_ok : planOk s7c16pGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s7c16pGX : List SVec := tensorPlanF 64 s7c16pGP (rootEightSrcXL 64)

/-- The representation of the target image. -/
def s7c16pW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet s7c16pG, ShortData.ofList s7c16pGT, 1 / 128,
    tensorRat 64 s7c16pGX ((tensorWordDenAll s7c16pG : ℚ) * 32)⟩

/-- The coordinates of the target image. -/
theorem s7c16pW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c16pG)
    (generatedAxisGlobalTwelveRepresentative 9)) = s7c16pW.real := by
  have hT := (tensorPlanF_actual s7c16pGP s7c16pGP_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [s7c16pGP_word, s7c16pG_growth]; norm_num) 32).2
  rw [s7c16pGP_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) s7c16pGW s7c16pG_check s7c16pGD s7c16pGD_ok
      s7c16pGD_cols
    s7c16pGD_rows s7c16pGT s7c16pGT_check _ hT _ (rootEightSrcL_rep (w := 64) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
