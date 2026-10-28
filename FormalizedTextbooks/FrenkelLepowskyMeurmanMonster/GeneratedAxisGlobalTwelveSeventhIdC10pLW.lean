/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10pChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10pChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP

/-! # Representations of both sides of the identification Seventh cell record S7c10+
(gforest:S7c10+, e = 1)

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
def s7c10pHP : List TPlan := [.letter (.xi),
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
theorem s7c10pHP_word : planWord s7c10pHP = s7c10pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s7c10pHP_ok : planOk s7c10pHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s7c10pHX : List SVec := tensorPlanF 72 s7c10pHP (srcSeventhX0F 72)

/-- The representation of the source image. -/
def s7c10pL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c10pH, ShortData.ofList s7c10pHT, 1 / srcSeventhD0,
    tensorRat 72 s7c10pHX ((tensorWordDenAll s7c10pH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c10pL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c10pH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c10pL.real := by
  have hT := (tensorPlanF_actual s7c10pHP s7c10pHP_ok (srcSeventhX0F_bnd (w := 72) (by norm_num))
    (by rw [s7c10pHP_word, s7c10pH_growth]; norm_num) srcSeventhD0).2
  rw [s7c10pHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 72) s7c10pHW s7c10pH_check s7c10pHD s7c10pHD_ok
      s7c10pHD_cols
    s7c10pHD_rows s7c10pHT s7c10pHT_check _ hT _ (seventhSrcGF_rep (w := 72) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c10pGP : List TPlan := [.letter (.qel (qmElt (15495652, false))),
    .letter (.sign 652 0),
    .run
      [(1, false), (0, true), (1, false), (0, true), (0, true), (1, false), (0, false),
        (0, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, false),
        (0, false), (1, false), (0, true), (1, false), (0, true), (0, true), (1, false),
        (0, true), (0, true), (0, true), (1, true), (0, true), (0, true), (1, true),
        (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, true),
        (0, true), (0, true), (1, true), (0, true), (1, true), (0, true), (0, true),
        (0, true), (1, true), (0, false), (1, true), (0, false), (0, false), (1, false),
        (0, false), (0, false), (1, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, true), (1, false), (0, false), (0, false), (1, false), (0, true), (1, false),
        (0, false), (0, false)]
      [.trans 0 2, .trans 0 11, .trans 1 0, .trans 1 2, .trans 3 2, .trans 2 0, .trans 2 1,
        .trans 2 3, .trans 2 11, .trans 3 0, .trans 6 4, .trans 4 6, .trans 7 5,
        .trans 5 0, .trans 5 1, .trans 5 2, .trans 5 3, .trans 5 4, .trans 5 7,
        .trans 9 6, .trans 6 0, .trans 6 1, .trans 6 5, .trans 6 9, .trans 8 7,
        .trans 7 0, .trans 7 3, .trans 7 4, .trans 7 5, .trans 7 8, .trans 8 1,
        .trans 8 2, .trans 8 6, .trans 8 7, .trans 8 9, .trans 9 1, .trans 9 3,
        .trans 9 4, .trans 9 6, .trans 9 8, .trans 10 4, .trans 10 11],
    .letter (.xi),
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

/-- The plan expands to the target word. -/
theorem s7c10pGP_word : planWord s7c10pGP = s7c10pG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s7c10pGP_ok : planOk s7c10pGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s7c10pGX : List SVec := tensorPlanF 72 s7c10pGP (srcSeventhX0F 72)

/-- The representation of the target image. -/
def s7c10pW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c10pG, ShortData.ofList s7c10pGT, 1 / srcSeventhD0,
    tensorRat 72 s7c10pGX ((tensorWordDenAll s7c10pG : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the target image. -/
theorem s7c10pW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c10pG)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c10pW.real := by
  have hT := (tensorPlanF_actual s7c10pGP s7c10pGP_ok (srcSeventhX0F_bnd (w := 72) (by norm_num))
    (by rw [s7c10pGP_word, s7c10pG_growth]; norm_num) srcSeventhD0).2
  rw [s7c10pGP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 72) s7c10pGW s7c10pG_check s7c10pGD s7c10pGD_ok
      s7c10pGD_cols
    s7c10pGD_rows s7c10pGT s7c10pGT_check _ hT _ (seventhSrcGF_rep (w := 72) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
