/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataF15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM

/-! # Data checks of the Fourth identification (F15-)

Both sides are local images of the Fourth axis: their representations are computed from
`fourthSrcVecW 72` (matrix block by the spatial alphabet, short block by a checked transport onto
the literal target lists of `GeneratedAxisGlobalTwelveFourthIdentDataF15`, tensor block by packed
words).  This module certifies the literal data and binds both representations to the genuine
coordinates; the pairing is evaluated in `GeneratedAxisGlobalTwelveFourthIdentF15`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of the image of the Fourth axis under the source word. -/
def fourthF15HX : List SVec := tensorWordAll 72 fourthF15H (fourthSrcXW 72)

/-- The packed tensor of the image of the Fourth axis under the target word. -/
def fourthF15GX : List SVec := tensorWordAll 72 fourthF15G (fourthSrcXW 72)

/-- The representation of the image of the Fourth axis under the source word. -/
def fourthF15L : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthF15H, ShortData.ofList fourthF15HT, 1 / 8,
    tensorRat 72 fourthF15HX ((tensorWordDenAll fourthF15H : ℚ) * 1)⟩

/-- The representation of the image of the Fourth axis under the target word. -/
def fourthF15W : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthF15G, ShortData.ofList fourthF15GT, 1 / 8,
    tensorRat 72 fourthF15GX ((tensorWordDenAll fourthF15G : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthF15H_check :
    (fourthWordData fourthF15H).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthF15G_check :
    (fourthWordData fourthF15G).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthF15D_ok : fourthF15HD.ok = true ∧ fourthF15GD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthF15HD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthF15H).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthF15HD.colsP i.val, fourthF15HD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthF15GD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordData fourthF15G).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthF15GD.colsP i.val, fourthF15GD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthF15HD_rows : ∀ i : Fin 24,
    fld 24 fourthF15HD.rowsP i.val = rowsOf (fun j => fld 24 fourthF15HD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthF15GD_rows : ∀ i : Fin 24,
    fld 24 fourthF15GD.rowsP i.val = rowsOf (fun j => fld 24 fourthF15GD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem fourthF15HT_check : shortCheckF fourthF15HD fourthSrcShort.flat fourthF15HT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem fourthF15GT_check : shortCheckF fourthF15GD fourthSrcShort.flat fourthF15GT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthF15T_labels : fourthF15HT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthF15GT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthF15H_growth : tensorWordGrowthAll fourthF15H * 56 = 29360128 := by decide

/-- The word bound of the target word. -/
theorem fourthF15G_growth : tensorWordGrowthAll fourthF15G * 56 = 29360128 := by decide

/-- The coordinates of the source image. -/
theorem fourthF15L_actual : griessConwayEncode (rhoLocal (identWordLocal fourthF15H)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthF15L.real := by
  have hT := (tensorWordAll_actual fourthF15H (fourthSrcXW_bnd (w := 72) (by norm_num))
    (by rw [fourthF15H_growth]; norm_num) 1).2
  rw [← fourthWordData_fst fourthF15H] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 72) (fourthWordData fourthF15H) fourthF15H_check
    fourthF15HD fourthF15D_ok.1 fourthF15HD_cols fourthF15HD_rows fourthF15HT fourthF15HT_check _
    hT _ (fourthSrcW_rep (by norm_num))

/-- The coordinates of the target image. -/
theorem fourthF15W_actual : griessConwayEncode (rhoLocal (identWordLocal fourthF15G)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthF15W.real := by
  have hT := (tensorWordAll_actual fourthF15G (fourthSrcXW_bnd (w := 72) (by norm_num))
    (by rw [fourthF15G_growth]; norm_num) 1).2
  rw [← fourthWordData_fst fourthF15G] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 72) (fourthWordData fourthF15G) fourthF15G_check
    fourthF15GD fourthF15D_ok.2 fourthF15GD_cols fourthF15GD_rows fourthF15GT fourthF15GT_check _
    hT _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
