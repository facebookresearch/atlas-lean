/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19pChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP

/-! # Representations of both sides of the identification Seventh cell record S7c19+
(gforest:S7c19+, e = 1)

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
def s7c19pHP : List TPlan := [.letter (.xi), .letter (.mono (0, true)), .letter (.xi), .letter
    (.xi), .letter (.mono (1, true)), .letter (.mono (0, false))]

/-- The plan expands to the source word. -/
theorem s7c19pHP_word : planWord s7c19pHP = s7c19pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s7c19pHP_ok : planOk s7c19pHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s7c19pHX : List SVec := tensorPlanF 72 s7c19pHP (srcSeventhX0F 72)

/-- The representation of the source image. -/
def s7c19pL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c19pH, ShortData.ofList s7c19pHT, 1 / srcSeventhD0,
    tensorRat 72 s7c19pHX ((tensorWordDenAll s7c19pH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c19pL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c19pH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c19pL.real := by
  have hT := (tensorPlanF_actual s7c19pHP s7c19pHP_ok (srcSeventhX0F_bnd (w := 72) (by norm_num))
    (by rw [s7c19pHP_word, s7c19pH_growth]; norm_num) srcSeventhD0).2
  rw [s7c19pHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 72) s7c19pHW s7c19pH_check s7c19pHD s7c19pHD_ok
      s7c19pHD_cols
    s7c19pHD_rows s7c19pHT s7c19pHT_check _ hT _ (seventhSrcGF_rep (w := 72) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c19pGP : List TPlan := [.letter (.qel (qmElt (16574396, true))), .letter (.sign 1980 0),
    .letter (.xi), .letter (.mono (0, true)), .letter (.xi), .letter (.xi), .letter (.mono (1,
    true)), .letter (.mono (0, false))]

/-- The plan expands to the target word. -/
theorem s7c19pGP_word : planWord s7c19pGP = s7c19pG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s7c19pGP_ok : planOk s7c19pGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s7c19pGX : List SVec := tensorPlanF 72 s7c19pGP (srcSeventhX0F 72)

/-- The representation of the target image. -/
def s7c19pW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c19pG, ShortData.ofList s7c19pGT, 1 / srcSeventhD0,
    tensorRat 72 s7c19pGX ((tensorWordDenAll s7c19pG : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the target image. -/
theorem s7c19pW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c19pG)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c19pW.real := by
  have hT := (tensorPlanF_actual s7c19pGP s7c19pGP_ok (srcSeventhX0F_bnd (w := 72) (by norm_num))
    (by rw [s7c19pGP_word, s7c19pG_growth]; norm_num) srcSeventhD0).2
  rw [s7c19pGP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 72) s7c19pGW s7c19pG_check s7c19pGD s7c19pGD_ok
      s7c19pGD_cols
    s7c19pGD_rows s7c19pGT s7c19pGT_check _ hT _ (seventhSrcGF_rep (w := 72) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
