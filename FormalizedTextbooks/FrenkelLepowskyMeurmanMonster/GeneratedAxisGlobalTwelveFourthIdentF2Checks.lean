/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataF2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM

/-! # Data checks of the Fourth identification (F2-)

Both sides are local images of the Fourth axis: their representations are computed from
`fourthSrcVecW 64` (matrix block by the spatial alphabet, short block by a checked transport onto
the literal target lists of `GeneratedAxisGlobalTwelveFourthIdentDataF2`, tensor block by packed
words).  This module certifies the literal data and binds both representations to the genuine
coordinates; the pairing is evaluated in `GeneratedAxisGlobalTwelveFourthIdentF2`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of the image of the Fourth axis under the source word. -/
def fourthF2HX : List SVec := tensorWordAll 64 fourthF2H (fourthSrcXW 64)

/-- The packed tensor of the image of the Fourth axis under the target word. -/
def fourthF2GX : List SVec := tensorWordAll 64 fourthF2G (fourthSrcXW 64)

/-- The representation of the image of the Fourth axis under the source word. -/
def fourthF2L : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthF2H, ShortData.ofList fourthF2HT, 1 / 8,
    tensorRat 64 fourthF2HX ((tensorWordDenAll fourthF2H : ℚ) * 1)⟩

/-- The representation of the image of the Fourth axis under the target word. -/
def fourthF2W : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthF2G, ShortData.ofList fourthF2GT, 1 / 8,
    tensorRat 64 fourthF2GX ((tensorWordDenAll fourthF2G : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthF2H_check :
    (fourthWordData fourthF2H).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthF2G_check :
    (fourthWordData fourthF2G).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthF2D_ok : fourthF2HD.ok = true ∧ fourthF2GD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthF2HD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthF2H).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthF2HD.colsP i.val, fourthF2HD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthF2GD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthF2G).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthF2GD.colsP i.val, fourthF2GD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthF2HD_rows : ∀ i : Fin 24,
    fld 24 fourthF2HD.rowsP i.val = rowsOf (fun j => fld 24 fourthF2HD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthF2GD_rows : ∀ i : Fin 24,
    fld 24 fourthF2GD.rowsP i.val = rowsOf (fun j => fld 24 fourthF2GD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem fourthF2HT_check : shortCheckF fourthF2HD fourthSrcShort.flat fourthF2HT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem fourthF2GT_check : shortCheckF fourthF2GD fourthSrcShort.flat fourthF2GT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthF2T_labels : fourthF2HT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthF2GT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthF2H_growth : tensorWordGrowthAll fourthF2H * 56 = 3670016 := by decide

/-- The word bound of the target word. -/
theorem fourthF2G_growth : tensorWordGrowthAll fourthF2G * 56 = 29360128 := by decide

/-- The coordinates of the source image. -/
theorem fourthF2L_actual : griessConwayEncode (rhoLocal (identWordLocal fourthF2H)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthF2L.real := by
  have hT := (tensorWordAll_actual fourthF2H (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF2H_growth]; norm_num) 1).2
  rw [← fourthWordData_fst fourthF2H] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordData fourthF2H) fourthF2H_check
    fourthF2HD fourthF2D_ok.1 fourthF2HD_cols fourthF2HD_rows fourthF2HT fourthF2HT_check _
    hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the target image. -/
theorem fourthF2W_actual : griessConwayEncode (rhoLocal (identWordLocal fourthF2G)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthF2W.real := by
  have hT := (tensorWordAll_actual fourthF2G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF2G_growth]; norm_num) 1).2
  rw [← fourthWordData_fst fourthF2G] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordData fourthF2G) fourthF2G_check
    fourthF2GD fourthF2D_ok.2 fourthF2GD_cols fourthF2GD_rows fourthF2GT fourthF2GT_check _
    hT _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
