/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataF1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM

/-! # Data checks of the Fourth identification (F1+)

Both sides are local images of the Fourth axis: their representations are computed from
`fourthSrcVecW 64` (matrix block by the spatial alphabet, short block by a checked transport onto
the literal target lists of `GeneratedAxisGlobalTwelveFourthIdentDataF1`, tensor block by packed
words).  This module certifies the literal data and binds both representations to the genuine
coordinates; the pairing is evaluated in `GeneratedAxisGlobalTwelveFourthIdentF1`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of the image of the Fourth axis under the source word. -/
def fourthF1HX : List SVec := tensorWordAll 64 fourthF1H (fourthSrcXW 64)

/-- The packed tensor of the image of the Fourth axis under the target word. -/
def fourthF1GX : List SVec := tensorWordAll 64 fourthF1G (fourthSrcXW 64)

/-- The representation of the image of the Fourth axis under the source word. -/
def fourthF1L : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthF1H, ShortData.ofList fourthF1HT, 1 / 8,
    tensorRat 64 fourthF1HX ((tensorWordDenAll fourthF1H : ℚ) * 1)⟩

/-- The representation of the image of the Fourth axis under the target word. -/
def fourthF1W : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthF1G, ShortData.ofList fourthF1GT, 1 / 8,
    tensorRat 64 fourthF1GX ((tensorWordDenAll fourthF1G : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthF1H_check :
    (fourthWordData fourthF1H).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthF1G_check :
    (fourthWordData fourthF1G).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthF1D_ok : fourthF1HD.ok = true ∧ fourthF1GD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthF1HD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthF1H).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthF1HD.colsP i.val, fourthF1HD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthF1GD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthF1G).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthF1GD.colsP i.val, fourthF1GD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthF1HD_rows : ∀ i : Fin 24,
    fld 24 fourthF1HD.rowsP i.val = rowsOf (fun j => fld 24 fourthF1HD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthF1GD_rows : ∀ i : Fin 24,
    fld 24 fourthF1GD.rowsP i.val = rowsOf (fun j => fld 24 fourthF1GD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem fourthF1HT_check : shortCheckF fourthF1HD fourthSrcShort.flat fourthF1HT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem fourthF1GT_check : shortCheckF fourthF1GD fourthSrcShort.flat fourthF1GT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthF1T_labels : fourthF1HT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthF1GT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthF1H_growth : tensorWordGrowthAll fourthF1H * 56 = 14336 := by decide

/-- The word bound of the target word. -/
theorem fourthF1G_growth : tensorWordGrowthAll fourthF1G * 56 = 29360128 := by decide

/-- The coordinates of the source image. -/
theorem fourthF1L_actual : griessConwayEncode (rhoLocal (identWordLocal fourthF1H)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthF1L.real := by
  have hT := (tensorWordAll_actual fourthF1H (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF1H_growth]; norm_num) 1).2
  rw [← fourthWordData_fst fourthF1H] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordData fourthF1H) fourthF1H_check
    fourthF1HD fourthF1D_ok.1 fourthF1HD_cols fourthF1HD_rows fourthF1HT fourthF1HT_check _
    hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the target image. -/
theorem fourthF1W_actual : griessConwayEncode (rhoLocal (identWordLocal fourthF1G)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthF1W.real := by
  have hT := (tensorWordAll_actual fourthF1G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF1G_growth]; norm_num) 1).2
  rw [← fourthWordData_fst fourthF1G] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordData fourthF1G) fourthF1G_check
    fourthF1GD fourthF1D_ok.2 fourthF1GD_cols fourthF1GD_rows fourthF1GT fourthF1GT_check _
    hT _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
