/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC13pChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC13pChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSeventhP

/-! # Representations of both sides of the identification Seventh cell record S7c13+
(gforest:S7c13+, e = 1)

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
def s7c13pHP : List TPlan := [.letter (.xi), .letter (.xi), .letter (.mono (1, true)), .letter
    (.mono (0, true)), .letter (.xi), .letter (.mono (1, true)), .letter (.mono (0, false))]

/-- The plan expands to the source word. -/
theorem s7c13pHP_word : planWord s7c13pHP = s7c13pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s7c13pHP_ok : planOk s7c13pHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s7c13pHX : List SVec := tensorPlanF 64 s7c13pHP (srcSeventhX0F 64)

/-- The representation of the source image. -/
def s7c13pL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c13pH, ShortData.ofList s7c13pHT, 1 / srcSeventhD0,
    tensorRat 64 s7c13pHX ((tensorWordDenAll s7c13pH : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the source image. -/
theorem s7c13pL_actual : griessConwayEncode (rhoLocal (identWordLocal s7c13pH)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c13pL.real := by
  have hT := (tensorPlanF_actual s7c13pHP s7c13pHP_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [s7c13pHP_word, s7c13pH_growth]; norm_num) srcSeventhD0).2
  rw [s7c13pHP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 64) s7c13pHW s7c13pH_check s7c13pHD s7c13pHD_ok
      s7c13pHD_cols
    s7c13pHD_rows s7c13pHT s7c13pHT_check _ hT _ (seventhSrcGF_rep (w := 64) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s7c13pGP : List TPlan := [.letter (.qel (qmElt (10665392, true))), .letter (.sign 1471 0),
    .letter (.xi), .letter (.xi), .letter (.mono (1, true)), .letter (.mono (0, true)), .letter
    (.xi), .letter (.mono (1, true)), .letter (.mono (0, false))]

/-- The plan expands to the target word. -/
theorem s7c13pGP_word : planWord s7c13pGP = s7c13pG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s7c13pGP_ok : planOk s7c13pGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s7c13pGX : List SVec := tensorPlanF 64 s7c13pGP (srcSeventhX0F 64)

/-- The representation of the target image. -/
def s7c13pW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet s7c13pG, ShortData.ofList s7c13pGT, 1 / srcSeventhD0,
    tensorRat 64 s7c13pGX ((tensorWordDenAll s7c13pG : ℚ) * srcSeventhD0)⟩

/-- The coordinates of the target image. -/
theorem s7c13pW_actual : griessConwayEncode (rhoLocal (identWordLocal s7c13pG)
    (generatedAxisGlobalTwelveRepresentative 6)) = s7c13pW.real := by
  have hT := (tensorPlanF_actual s7c13pGP s7c13pGP_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [s7c13pGP_word, s7c13pG_growth]; norm_num) srcSeventhD0).2
  rw [s7c13pGP_word] at hT
  exact IdentVec.word_actual (seventhSrcVecGF 64) s7c13pGW s7c13pG_check s7c13pGD s7c13pGD_ok
      s7c13pGD_cols
    s7c13pGD_rows s7c13pGT s7c13pGT_check _ hT _ (seventhSrcGF_rep (w := 64) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
