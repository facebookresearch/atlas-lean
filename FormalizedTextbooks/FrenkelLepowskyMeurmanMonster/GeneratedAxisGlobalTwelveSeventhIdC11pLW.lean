/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC11pChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC11pChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Representations of both sides of the identification Seventh cell record S7c11+
(gforest:S7c11+, e = 1)

The two images are computed from the source vector (matrix block by the spatial alphabet, short
block by the
checked transports, tensor block by fast tensor plans) and bound to the genuine coordinates of the
local images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The tensor plan of the source word (one step per letter, fast Xi letter). -/
def s7c11pHP : List TPlan := [.letter (.xi), .letter (.xi), .letter (.mono (1, true)), .letter
    (.mono (0, true)), .letter (.xi), .letter (.mono (1, true))]

/-- The plan expands to the source word. -/
theorem s7c11pHP_word : planWord s7c11pHP = s7c11pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s7c11pHP_ok : planOk s7c11pHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s7c11pHX : List SVec := tensorPlanF 64 s7c11pHP (srcSeventhX0F 64)

/-- The representation of the source image. -/
def s7c11pL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c11pH, ShortData.ofList s7c11pHT, 1 / srcSeventhD0,
    tensorRat 64 s7c11pHX ((tensorWordDenAll s7c11pH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c11pL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c11pH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c11pL.real := by
  have hT := (tensorPlanF_actual s7c11pHP s7c11pHP_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [s7c11pHP_word, s7c11pH_growth]; norm_num) srcSeventhD0).2
  rw [s7c11pHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 64) s7c11pHW s7c11pH_check s7c11pHD s7c11pHD_ok
      s7c11pHD_cols
    s7c11pHD_rows s7c11pHT s7c11pHT_check _ hT _ (seventhSrcGF_rep (w := 64) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c11pGP : List TPlan := [.letter (.qel (qmElt (9965384, false))),
    .letter (.sign 902 0),
    .run
      [(0, false), (1, false), (0, true), (1, false), (0, false), (1, false), (0, false),
        (0, false), (0, false), (1, false), (0, true), (1, false), (0, false),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (0, false), (0, false), (0, false),
        (0, false), (1, true), (0, true), (0, true), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, true), (0, true), (0, true), (1, true), (0, true),
        (0, true), (0, true), (1, true), (0, false), (0, false), (1, true), (0, false),
        (1, true), (0, false), (0, false), (1, false), (0, false), (1, false), (0, true),
        (0, true), (1, false), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, false), (1, false), (0, false), (0, false), (1, false), (0, true), (0, true),
        (1, false), (0, true), (0, true), (0, true)]
      [.trans 0 3, .trans 3 2, .trans 3 1, .trans 6 9, .trans 9 8, .trans 9 7, .trans 6 0,
        .trans 5 8, .trans 8 9, .trans 7 4, .trans 9 1, .trans 3 0, .trans 0 3,
        .trans 9 6, .trans 10 7, .trans 4 7, .trans 9 4, .trans 4 2, .trans 4 9,
        .trans 6 5, .trans 5 6, .trans 7 5, .trans 6 3, .trans 5 4, .trans 7 1,
        .trans 4 1, .trans 1 0, .trans 3 11, .trans 0 2, .trans 2 1, .trans 10 11,
        .trans 0 11, .trans 1 11],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, false)]
      [.trans 10 11, .trans 0 10, .trans 1 6, .trans 4 1, .trans 1 0, .trans 10 4, .trans 4 3,
        .trans 1 2, .trans 9 10, .trans 6 0, .trans 0 5, .trans 4 6, .trans 6 1,
        .trans 7 1, .trans 2 1, .trans 1 4, .trans 10 11, .trans 0 7, .trans 3 6,
        .trans 1 8, .trans 8 3, .trans 8 9, .trans 9 2, .trans 2 9, .trans 9 2,
        .trans 0 11, .trans 3 8, .trans 4 5, .trans 5 0, .trans 5 9, .trans 5 11,
        .trans 6 0, .trans 6 7, .trans 6 11, .trans 7 3, .trans 7 8, .trans 8 3,
        .trans 8 4, .trans 8 5, .trans 8 6, .trans 8 7, .trans 8 9]]

/-- The plan expands to the target word. -/
theorem s7c11pGP_word : planWord s7c11pGP = s7c11pG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s7c11pGP_ok : planOk s7c11pGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s7c11pGX : List SVec := tensorPlanF 64 s7c11pGP (twelfthSrcXW 64)

/-- The representation of the target image. -/
def s7c11pW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet s7c11pG, ShortData.ofList s7c11pGT, 1 / 128,
    tensorRat 64 s7c11pGX ((tensorWordDenAll s7c11pG : ℚ) * 32)⟩

/-- The coordinates of the target image. -/
theorem s7c11pW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c11pG)
    (generatedAxisGlobalTwelveRepresentative 10)) = s7c11pW.real := by
  have hT := (tensorPlanF_actual s7c11pGP s7c11pGP_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [s7c11pGP_word, s7c11pG_growth]; norm_num) 32).2
  rw [s7c11pGP_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) s7c11pGW s7c11pG_check s7c11pGD s7c11pGD_ok
      s7c11pGD_cols
    s7c11pGD_rows s7c11pGT s7c11pGT_check _ hT _ (twelfthSrcS_rep (w := 64) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
