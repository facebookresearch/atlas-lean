/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentDataP12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctGM

/-! # Data checks of the partner identification `F12+` (Fifth coset 3 to Fourth)

The source side is a local image of the Fifth axis (`fifthSrcVecW 64`), the target side a local
image of the Fourth axis (`fourthSrcVecW 64`); both representations are computed by the word
actions and bound to the genuine coordinates here.  The pairing is evaluated in
`GeneratedAxisGlobalTwelveFourthIdentP12`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of the image of the Fifth axis under the source word. -/
def fourthP12HX : List SVec := tensorWordAll 64 fourthP12H (fifthSrcXW 64)

/-- The packed tensor of the image of the Fourth axis under the target word. -/
def fourthP12GX : List SVec := tensorWordAll 64 fourthP12G (fourthSrcXW 64)

/-- The representation of the source image (Fifth axis). -/
def fourthP12L : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet fourthP12H, ShortData.ofList fourthP12HT, 1 / 16,
    tensorRat 64 fourthP12HX ((tensorWordDenAll fourthP12H : ℚ) * 1)⟩

/-- The representation of the target image (Fourth axis). -/
def fourthP12W : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet fourthP12G, ShortData.ofList fourthP12GT, 1 / 8,
    tensorRat 64 fourthP12GX ((tensorWordDenAll fourthP12G : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem fourthP12H_check :
    (fourthWordDataQ fourthP12H).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem fourthP12G_check :
    (fourthWordDataQ fourthP12G).all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem fourthP12D_ok : fourthP12HD.ok = true ∧ fourthP12GD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem fourthP12HD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordDataQ fourthP12H).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthP12HD.colsP i.val, fourthP12HD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem fourthP12GD_cols : ∀ i : Fin 24,
    qmWordP ((fourthWordDataQ fourthP12G).map Prod.snd) (2 ^ i.val, false) =
      (fld 24 fourthP12GD.colsP i.val, fourthP12GD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem fourthP12HD_rows : ∀ i : Fin 24,
    fld 24 fourthP12HD.rowsP i.val = rowsOf (fun j => fld 24 fourthP12HD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem fourthP12GD_rows : ∀ i : Fin 24,
    fld 24 fourthP12GD.rowsP i.val = rowsOf (fun j => fld 24 fourthP12GD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem fourthP12HT_check : shortCheckF fourthP12HD fifthSrcShort.flat fourthP12HT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem fourthP12GT_check : shortCheckF fourthP12GD fourthSrcShort.flat fourthP12GT = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem fourthP12T_labels : fourthP12HT.all (fun p => decide (p.1 < 98280)) = true ∧
    fourthP12GT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem fourthP12H_growth : tensorWordGrowthAll fourthP12H * 64 = 4194304 := by decide

/-- The word bound of the target word. -/
theorem fourthP12G_growth : tensorWordGrowthAll fourthP12G * 56 = 114688 := by decide

/-- The coordinates of the source image. -/
theorem fourthP12L_actual : griessConwayEncode (rhoLocal (identWordLocal fourthP12H)
    (generatedAxisGlobalTwelveRepresentative 4)) = fourthP12L.real := by
  have hT := (tensorWordAll_actual fourthP12H (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthP12H_growth]; norm_num) 1).2
  rw [← fourthWordDataQ_fst fourthP12H] at hT ⊢
  exact IdentVec.word_actual (fifthSrcVecW 64) (fourthWordDataQ fourthP12H) fourthP12H_check
    fourthP12HD fourthP12D_ok.1 fourthP12HD_cols fourthP12HD_rows fourthP12HT fourthP12HT_check _
    hT _ (fifthSrcW_rep (by norm_num))

/-- The coordinates of the target image. -/
theorem fourthP12W_actual : griessConwayEncode (rhoLocal (identWordLocal fourthP12G)
    (generatedAxisGlobalTwelveRepresentative 3)) = fourthP12W.real := by
  have hT := (tensorWordAll_actual fourthP12G (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [fourthP12G_growth]; norm_num) 1).2
  rw [← fourthWordDataQ_fst fourthP12G] at hT ⊢
  exact IdentVec.word_actual (fourthSrcVecW 64) (fourthWordDataQ fourthP12G) fourthP12G_check
    fourthP12GD fourthP12D_ok.2 fourthP12GD_cols fourthP12GD_rows fourthP12GT fourthP12GT_check _
    hT _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
