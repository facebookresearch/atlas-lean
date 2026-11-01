/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC6pChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC6pChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Representations of both sides of the identification Seventh cell record S7c6+
(gforest:S7c6+, e = 1)

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
def s7c6pHP : List TPlan := [.letter (.xi),
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
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11]]

/-- The plan expands to the source word. -/
theorem s7c6pHP_word : planWord s7c6pHP = s7c6pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s7c6pHP_ok : planOk s7c6pHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s7c6pHX : List SVec := tensorPlanF 64 s7c6pHP (srcSeventhX0F 64)

/-- The representation of the source image. -/
def s7c6pL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c6pH, ShortData.ofList s7c6pHT, 1 / srcSeventhD0,
    tensorRat 64 s7c6pHX ((tensorWordDenAll s7c6pH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c6pL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c6pH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c6pL.real := by
  have hT := (tensorPlanF_actual s7c6pHP s7c6pHP_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [s7c6pHP_word, s7c6pH_growth]; norm_num) srcSeventhD0).2
  rw [s7c6pHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 64) s7c6pHW s7c6pH_check s7c6pHD s7c6pHD_ok
      s7c6pHD_cols
    s7c6pHD_rows s7c6pHT s7c6pHT_check _ hT _ (seventhSrcGF_rep (w := 64) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c6pGP : List TPlan := [.letter (.qel (qmElt (13381462, true))),
    .letter (.sign 1515 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, true), (1, false), (0, true), (0, true), (0, true),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, true), (0, true),
        (0, true), (1, true), (0, false), (0, false), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, true),
        (0, true), (1, true), (0, false), (1, true), (0, false), (0, false), (1, true),
        (0, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false),
        (0, false), (0, false), (1, false), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, true),
        (0, true), (1, false), (0, false), (0, false), (1, false)]
      [.trans 0 1, .trans 0 2, .trans 0 3, .trans 0 4, .trans 0 6, .trans 0 8, .trans 2 1,
        .trans 1 0, .trans 1 2, .trans 1 3, .trans 1 4, .trans 4 2, .trans 2 0,
        .trans 2 4, .trans 2 6, .trans 2 8, .trans 6 3, .trans 3 2, .trans 3 6,
        .trans 3 8, .trans 8 4, .trans 4 0, .trans 4 1, .trans 4 2, .trans 4 3,
        .trans 4 8, .trans 5 0, .trans 5 3, .trans 5 6, .trans 5 7, .trans 5 9,
        .trans 5 10, .trans 6 3, .trans 6 4, .trans 6 7, .trans 6 8, .trans 6 9,
        .trans 6 10, .trans 8 7, .trans 7 1, .trans 7 6, .trans 7 8, .trans 8 2,
        .trans 8 6, .trans 8 7, .trans 8 9, .trans 10 9, .trans 9 0, .trans 9 1,
        .trans 9 3, .trans 9 7, .trans 9 8, .trans 9 10, .trans 10 1, .trans 10 2,
        .trans 10 6, .trans 10 8],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi),
    .letter (.xi),
    .letter (.sign 32 0),
    .run
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11]]

/-- The plan expands to the target word. -/
theorem s7c6pGP_word : planWord s7c6pGP = s7c6pG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s7c6pGP_ok : planOk s7c6pGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s7c6pGX : List SVec := tensorPlanF 64 s7c6pGP (twelfthSrcXW 64)

/-- The representation of the target image. -/
def s7c6pW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet s7c6pG, ShortData.ofList s7c6pGT, 1 / 128,
    tensorRat 64 s7c6pGX ((tensorWordDenAll s7c6pG : ℚ) * 32)⟩

/-- The coordinates of the target image. -/
theorem s7c6pW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c6pG)
    (generatedAxisGlobalTwelveRepresentative 10)) = s7c6pW.real := by
  have hT := (tensorPlanF_actual s7c6pGP s7c6pGP_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [s7c6pGP_word, s7c6pG_growth]; norm_num) 32).2
  rw [s7c6pGP_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) s7c6pGW s7c6pG_check s7c6pGD s7c6pGD_ok
      s7c6pGD_cols
    s7c6pGD_rows s7c6pGT s7c6pGT_check _ hT _ (twelfthSrcS_rep (w := 64) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
