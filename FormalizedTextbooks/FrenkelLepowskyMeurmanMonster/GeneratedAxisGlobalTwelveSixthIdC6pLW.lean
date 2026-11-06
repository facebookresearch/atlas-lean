/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pChkH
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdC6pChkG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Representations of both sides of the identification Sixth cell record S6c6+ (gforest:S6c6+,
e = 1)

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
def s6c6pHP : List TPlan := [.letter (.xi), .letter (.xi), .letter (.mono (1, true)), .letter
    (.xi), .letter (.xi), .letter (.mono (0, true))]

/-- The plan expands to the source word. -/
theorem s6c6pHP_word : planWord s6c6pHP = s6c6pH := rfl

set_option maxRecDepth 100000 in
/-- The plan of the source word is admissible. -/
theorem s6c6pHP_ok : planOk s6c6pHP = true := by decide +kernel

/-- The packed tensor of the source image. -/
def s6c6pHX : List SVec := tensorPlanF 64 s6c6pHP (sixthSXF 64)

/-- The representation of the source image. -/
def s6c6pL : IdentVec :=
  ⟨sixthSrcMat.act identSpatialAlphabet s6c6pH, ShortData.ofList s6c6pHT, 1 / 32,
    tensorRat 64 s6c6pHX ((tensorWordDenAll s6c6pH : ℚ) * 32)⟩

/-- The coordinates of the source image. -/
theorem s6c6pL_actual : griessConwayEncode (rhoLocal (identWordLocal s6c6pH)
    (generatedAxisGlobalTwelveRepresentative 5)) = s6c6pL.real := by
  have hT := (tensorPlanF_actual s6c6pHP s6c6pHP_ok (sixthSXF_bndF (w := 64) (by norm_num))
    (by rw [s6c6pHP_word, s6c6pH_growth]; norm_num) 32).2
  rw [s6c6pHP_word] at hT
  exact IdentVec.word_actual (sixthSrcVecF 64) s6c6pHW s6c6pH_check s6c6pHD s6c6pHD_ok s6c6pHD_cols
    s6c6pHD_rows s6c6pHT s6c6pHT_check _ hT _ (sixthSrcF_rep (w := 64) (by norm_num))

/-- The tensor plan of the target word (one step per letter, fast Xi letter). -/
def s6c6pGP : List TPlan := [.letter (.qel (qmElt (13215488, false))), .letter (.sign 1792 0),
    .letter (.xi), .letter (.xi), .letter (.mono (1, true)), .letter (.xi), .letter (.xi), .letter
    (.mono (0, true))]

/-- The plan expands to the target word. -/
theorem s6c6pGP_word : planWord s6c6pGP = s6c6pG := rfl

set_option maxRecDepth 100000 in
/-- The plan of the target word is admissible. -/
theorem s6c6pGP_ok : planOk s6c6pGP = true := by decide +kernel

/-- The packed tensor of the target image. -/
def s6c6pGX : List SVec := tensorPlanF 64 s6c6pGP (sixthSXF 64)

/-- The representation of the target image. -/
def s6c6pW : IdentVec :=
  ⟨sixthSrcMat.act identSpatialAlphabet s6c6pG, ShortData.ofList s6c6pGT, 1 / 32,
    tensorRat 64 s6c6pGX ((tensorWordDenAll s6c6pG : ℚ) * 32)⟩

/-- The coordinates of the target image. -/
theorem s6c6pW_actual : griessConwayEncode (rhoLocal (identWordLocal s6c6pG)
    (generatedAxisGlobalTwelveRepresentative 5)) = s6c6pW.real := by
  have hT := (tensorPlanF_actual s6c6pGP s6c6pGP_ok (sixthSXF_bndF (w := 64) (by norm_num))
    (by rw [s6c6pGP_word, s6c6pG_growth]; norm_num) 32).2
  rw [s6c6pGP_word] at hT
  exact IdentVec.word_actual (sixthSrcVecF 64) s6c6pGW s6c6pG_check s6c6pGD s6c6pGD_ok s6c6pGD_cols
    s6c6pGD_rows s6c6pGT s6c6pGT_check _ hT _ (sixthSrcF_rep (w := 64) (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
