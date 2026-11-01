/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataF12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM

/-! # Data checks of the Fourth identification (F12-)

Both sides are local images of the Fourth axis: their representations are computed from
`fourthSrcVecW 64` (matrix block by the spatial alphabet, short block by a checked transport onto
the literal target lists of `GeneratedAxisGlobalTwelveFourthIdentDataF12`, tensor block by packed
words).  This module certifies the literal data and binds both representations to the genuine
coordinates; the pairing is evaluated in `GeneratedAxisGlobalTwelveFourthIdentF12`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of the image of the Fourth axis under the source word. -/
def fourthF12HX : List SVec := tensorWordAll 64 fourthF12H (fourthSrcXW 64)

/-- The packed tensor of the image of the Fourth axis under the target word. -/
def fourthF12GX : List SVec := tensorWordAll 64 fourthF12G (fourthSrcXW 64)

/-- The representation of the image of the Fourth axis under the source word. -/
def fourthF12L : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthF12H, ShortData.ofList fourthF12HT, 1 / 8,
    tensorRat 64 fourthF12HX ((tensorWordDenAll fourthF12H : ℚ) * 1)⟩

/-- The representation of the image of the Fourth axis under the target word. -/
def fourthF12W : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthF12G, ShortData.ofList fourthF12GT, 1 / 8,
    tensorRat 64 fourthF12GX ((tensorWordDenAll fourthF12G : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthF12H_check :
    (fourthWordData fourthF12H).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthF12G_check :
    (fourthWordData fourthF12G).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthF12D_ok : fourthF12HD.ok = true ∧ fourthF12GD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthF12HD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthF12H).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthF12HD.colsP i.val, fourthF12HD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthF12GD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthF12G).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthF12GD.colsP i.val, fourthF12GD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthF12HD_rows : ∀ i : Fin 24,
    fld 24 fourthF12HD.rowsP i.val = rowsOf (fun j => fld 24 fourthF12HD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthF12GD_rows : ∀ i : Fin 24,
    fld 24 fourthF12GD.rowsP i.val = rowsOf (fun j => fld 24 fourthF12GD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem fourthF12HT_check : shortCheckF fourthF12HD fourthSrcShort.flat fourthF12HT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem fourthF12GT_check : shortCheckF fourthF12GD fourthSrcShort.flat fourthF12GT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthF12T_labels : fourthF12HT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthF12GT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthF12H_growth : tensorWordGrowthAll fourthF12H * 56 = 114688 := by decide

/-- The word bound of the target word. -/
theorem fourthF12G_growth : tensorWordGrowthAll fourthF12G * 56 = 29360128 := by decide

/-- The coordinates of the source image. -/
theorem fourthF12L_actual : griessConwayEncode (rhoLocal (identWordLocal fourthF12H)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthF12L.real := by
  have hT := (tensorWordAll_actual fourthF12H (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF12H_growth]; norm_num) 1).2
  rw [← fourthWordData_fst fourthF12H] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordData fourthF12H) fourthF12H_check
    fourthF12HD fourthF12D_ok.1 fourthF12HD_cols fourthF12HD_rows fourthF12HT fourthF12HT_check _
    hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the target image. -/
theorem fourthF12W_actual : griessConwayEncode (rhoLocal (identWordLocal fourthF12G)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthF12W.real := by
  have hT := (tensorWordAll_actual fourthF12G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF12G_growth]; norm_num) 1).2
  rw [← fourthWordData_fst fourthF12G] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordData fourthF12G) fourthF12G_check
    fourthF12GD fourthF12D_ok.2 fourthF12GD_cols fourthF12GD_rows fourthF12GT fourthF12GT_check _
    hT _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
