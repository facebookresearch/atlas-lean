/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3pChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW

/-! # Representations of both sides of the identification Seventh cell record S7c3+
(gforest:S7c3+, e = 1)

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
def s7c3pHP : List TPlan := [.letter (.xi), .letter (.xi), .letter (.mono (1, true))]

/-- The plan expands to the source word. -/
theorem s7c3pHP_word : planWord s7c3pHP = s7c3pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s7c3pHP_ok : planOk s7c3pHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s7c3pHX : List SVec := tensorPlanF 64 s7c3pHP (srcSeventhX0F 64)

/-- The representation of the source image. -/
def s7c3pL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c3pH, ShortData.ofList s7c3pHT, 1 / srcSeventhD0,
    tensorRat 64 s7c3pHX ((tensorWordDenAll s7c3pH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c3pL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c3pH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c3pL.real := by
  have hT := (tensorPlanF_actual s7c3pHP s7c3pHP_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [s7c3pHP_word, s7c3pH_growth]; norm_num) srcSeventhD0).2
  rw [s7c3pHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 64) s7c3pHW s7c3pH_check s7c3pHD s7c3pHD_ok
      s7c3pHD_cols
    s7c3pHD_rows s7c3pHT s7c3pHT_check _ hT _ (seventhSrcGF_rep (w := 64) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c3pGP : List TPlan := [.letter (.qel (qmElt (2900176, true))),
    .letter (.sign 398 0),
    .run
      [(0, false), (0, false), (0, false), (1, false), (0, true), (0, true), (0, true),
        (1, false), (0, true), (1, false), (0, false), (0, false), (0, false),
        (1, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, false),
        (1, false), (0, false), (1, true), (0, false), (0, false), (0, false), (1, true),
        (0, false), (0, false), (1, true), (0, false), (1, true), (0, false), (0, false),
        (1, true), (0, true), (1, true), (0, true), (0, true), (1, true), (0, true),
        (0, true), (1, true), (0, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, false), (1, false), (0, true), (1, false), (0, false),
        (0, false), (1, false), (0, true), (0, true), (0, true), (1, false), (0, true),
        (1, false)]
      [.trans 3 8, .trans 0 4, .trans 1 6, .trans 6 3, .trans 2 0, .trans 7 5, .trans 8 0,
        .trans 0 1, .trans 10 9, .trans 9 10, .trans 10 8, .trans 1 2, .trans 4 2,
        .trans 1 8, .trans 8 6, .trans 6 2, .trans 2 6, .trans 2 7, .trans 1 7,
        .trans 1 3, .trans 7 10, .trans 3 1, .trans 1 3, .trans 10 0, .trans 10 4,
        .trans 10 9, .trans 9 2, .trans 9 5, .trans 5 0, .trans 0 6, .trans 6 4,
        .trans 6 1],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

/-- The plan expands to the target word. -/
theorem s7c3pGP_word : planWord s7c3pGP = s7c3pG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s7c3pGP_ok : planOk s7c3pGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s7c3pGX : List SVec := tensorPlanF 64 s7c3pGP (fifthSrcXW 64)

/-- The representation of the target image. -/
def s7c3pW : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet s7c3pG, ShortData.ofList s7c3pGT, 1 / 16,
    tensorRat 64 s7c3pGX ((tensorWordDenAll s7c3pG : ℚ) * 1)⟩

/-- The coordinates of the target image. -/
theorem s7c3pW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c3pG)
    (generatedAxisGlobalTwelveRepresentative 4)) = s7c3pW.real := by
  have hT := (tensorPlanF_actual s7c3pGP s7c3pGP_ok (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [s7c3pGP_word, s7c3pG_growth]; norm_num) 1).2
  rw [s7c3pGP_word] at hT
  exact IdentVec.word_actual (fifthSrcVecW 64) s7c3pGW s7c3pG_check s7c3pGD s7c3pGD_ok s7c3pGD_cols
    s7c3pGD_rows s7c3pGT s7c3pGT_check _ hT _ (fifthSrcW_rep (w := 64) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
