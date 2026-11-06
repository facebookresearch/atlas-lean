/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataP0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM

/-! # Data checks of the partner identification `F0+` (Fifth coset 0 to Fourth)

The source side is a local image of the Fifth axis (`fifthSrcVecW 64`), the target side a local
image of the Fourth axis (`fourthSrcVecW 64`); both representations are computed by the word
actions and bound to the genuine coordinates here.  The pairing is evaluated in
`GeneratedAxisGlobalTwelveFourthIdentP0`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of the image of the Fifth axis under the source word. -/
def fourthP0HX : List SVec := tensorWordAll 64 fourthP0H (fifthSrcXW 64)

/-- The packed tensor of the image of the Fourth axis under the target word. -/
def fourthP0GX : List SVec := tensorWordAll 64 fourthP0G (fourthSrcXW 64)

/-- The representation of the source image (Fifth axis). -/
def fourthP0L : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet fourthP0H, ShortData.ofList fourthP0HT, 1 / 16,
    tensorRat 64 fourthP0HX ((tensorWordDenAll fourthP0H : ℚ) * 1)⟩

/-- The representation of the target image (Fourth axis). -/
def fourthP0W : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthP0G, ShortData.ofList fourthP0GT, 1 / 8,
    tensorRat 64 fourthP0GX ((tensorWordDenAll fourthP0G : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthP0H_check :
    (fourthWordDataQ fourthP0H).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthP0G_check :
    (fourthWordDataQ fourthP0G).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthP0D_ok : fourthP0HD.ok = true ∧ fourthP0GD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthP0HD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordDataQ fourthP0H).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthP0HD.colsP i.val, fourthP0HD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthP0GD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordDataQ fourthP0G).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthP0GD.colsP i.val, fourthP0GD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthP0HD_rows : ∀ i : Fin 24,
    fld 24 fourthP0HD.rowsP i.val = rowsOf (fun j => fld 24 fourthP0HD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthP0GD_rows : ∀ i : Fin 24,
    fld 24 fourthP0GD.rowsP i.val = rowsOf (fun j => fld 24 fourthP0GD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem fourthP0HT_check : shortCheckF fourthP0HD fifthSrcShort.flat fourthP0HT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem fourthP0GT_check : shortCheckF fourthP0GD fourthSrcShort.flat fourthP0GT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthP0T_labels : fourthP0HT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthP0GT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthP0H_growth : tensorWordGrowthAll fourthP0H * 64 = 4194304 := by decide

/-- The word bound of the target word. -/
theorem fourthP0G_growth : tensorWordGrowthAll fourthP0G * 56 = 114688 := by decide

/-- The coordinates of the source image. -/
theorem fourthP0L_actual : griessConwayEncode (rhoLocal (identWordLocal fourthP0H)
    (generatedAxisGlobalTwelveRepresentative 4)) = fourthP0L.real := by
  have hT := (tensorWordAll_actual fourthP0H (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthP0H_growth]; norm_num) 1).2
  rw [← fourthWordDataQ_fst fourthP0H] at hT ⊢
  exact IdentVec.word_actual (fifthSrcVecW 64) (fourthWordDataQ fourthP0H) fourthP0H_check
    fourthP0HD fourthP0D_ok.1 fourthP0HD_cols fourthP0HD_rows fourthP0HT fourthP0HT_check _
    hT _ (fifthSrcW_rep (by norm_num))

/-- The coordinates of the target image. -/
theorem fourthP0W_actual : griessConwayEncode (rhoLocal (identWordLocal fourthP0G)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthP0W.real := by
  have hT := (tensorWordAll_actual fourthP0G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthP0G_growth]; norm_num) 1).2
  rw [← fourthWordDataQ_fst fourthP0G] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordDataQ fourthP0G) fourthP0G_check
    fourthP0GD fourthP0D_ok.2 fourthP0GD_cols fourthP0GD_rows fourthP0GT fourthP0GT_check _
    hT _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
