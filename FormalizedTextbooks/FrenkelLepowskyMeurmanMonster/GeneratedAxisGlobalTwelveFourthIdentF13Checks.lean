/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataF13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM

/-! # Data checks of the Fourth identification (F13-)

Both sides are local images of the Fourth axis: their representations are computed from
`fourthSrcVecW 64` (matrix block by the spatial alphabet, short block by a checked transport onto
the literal target lists of `GeneratedAxisGlobalTwelveFourthIdentDataF13`, tensor block by packed
words).  This module certifies the literal data and binds both representations to the genuine
coordinates; the pairing is evaluated in `GeneratedAxisGlobalTwelveFourthIdentF13`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of the image of the Fourth axis under the source word. -/
def fourthF13HX : List SVec := tensorWordAll 64 fourthF13H (fourthSrcXW 64)

/-- The packed tensor of the image of the Fourth axis under the target word. -/
def fourthF13GX : List SVec := tensorWordAll 64 fourthF13G (fourthSrcXW 64)

/-- The representation of the image of the Fourth axis under the source word. -/
def fourthF13L : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthF13H, ShortData.ofList fourthF13HT, 1 / 8,
    tensorRat 64 fourthF13HX ((tensorWordDenAll fourthF13H : ℚ) * 1)⟩

/-- The representation of the image of the Fourth axis under the target word. -/
def fourthF13W : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthF13G, ShortData.ofList fourthF13GT, 1 / 8,
    tensorRat 64 fourthF13GX ((tensorWordDenAll fourthF13G : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthF13H_check :
    (fourthWordData fourthF13H).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthF13G_check :
    (fourthWordData fourthF13G).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthF13D_ok : fourthF13HD.ok = true ∧ fourthF13GD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthF13HD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthF13H).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthF13HD.colsP i.val, fourthF13HD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthF13GD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthF13G).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthF13GD.colsP i.val, fourthF13GD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthF13HD_rows : ∀ i : Fin 24,
    fld 24 fourthF13HD.rowsP i.val = rowsOf (fun j => fld 24 fourthF13HD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthF13GD_rows : ∀ i : Fin 24,
    fld 24 fourthF13GD.rowsP i.val = rowsOf (fun j => fld 24 fourthF13GD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem fourthF13HT_check : shortCheckF fourthF13HD fourthSrcShort.flat fourthF13HT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem fourthF13GT_check : shortCheckF fourthF13GD fourthSrcShort.flat fourthF13GT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthF13T_labels : fourthF13HT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthF13GT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthF13H_growth : tensorWordGrowthAll fourthF13H * 56 = 3670016 := by decide

/-- The word bound of the target word. -/
theorem fourthF13G_growth : tensorWordGrowthAll fourthF13G * 56 = 29360128 := by decide

/-- The coordinates of the source image. -/
theorem fourthF13L_actual : griessConwayEncode (rhoLocal (identWordLocal fourthF13H)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthF13L.real := by
  have hT := (tensorWordAll_actual fourthF13H (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF13H_growth]; norm_num) 1).2
  rw [← fourthWordData_fst fourthF13H] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordData fourthF13H) fourthF13H_check
    fourthF13HD fourthF13D_ok.1 fourthF13HD_cols fourthF13HD_rows fourthF13HT fourthF13HT_check _
    hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the target image. -/
theorem fourthF13W_actual : griessConwayEncode (rhoLocal (identWordLocal fourthF13G)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthF13W.real := by
  have hT := (tensorWordAll_actual fourthF13G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthF13G_growth]; norm_num) 1).2
  rw [← fourthWordData_fst fourthF13G] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordData fourthF13G) fourthF13G_check
    fourthF13GD fourthF13D_ok.2 fourthF13GD_cols fourthF13GD_rows fourthF13GT fourthF13GT_check _
    hT _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
