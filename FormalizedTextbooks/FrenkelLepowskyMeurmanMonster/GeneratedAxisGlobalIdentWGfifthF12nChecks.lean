/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF12nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW

/-! # Factory checks of the identification Fifth[12]- <-> Fourth[2]- (record gfifth:F12-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words) and bound to the genuine coordinates of the two local images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGfifthF12nH : List IdentLetter := wGfifthF12nHW.map Prod.fst

/-- The target word. -/
def wGfifthF12nG : List IdentLetter := wGfifthF12nGW.map Prod.fst

/-- The packed tensor of the source image. -/
def wGfifthF12nHX : List SVec := tensorWordAll 64 wGfifthF12nH (fifthSrcXW 64)

/-- The packed tensor of the target image. -/
def wGfifthF12nGX : List SVec := tensorWordAll 64 wGfifthF12nG (fourthSrcXW 64)

/-- The representation of the source image. -/
def wGfifthF12nL : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet wGfifthF12nH, ShortData.ofList wGfifthF12nHT, 1 / 16,
    tensorRat 64 wGfifthF12nHX ((tensorWordDenAll wGfifthF12nH : ℚ) * 1)⟩

/-- The representation of the target image. -/
def wGfifthF12nW : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet wGfifthF12nG, ShortData.ofList wGfifthF12nGT, 1 / 8,
    tensorRat 64 wGfifthF12nGX ((tensorWordDenAll wGfifthF12nG : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGfifthF12nH_check : wGfifthF12nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGfifthF12nG_check : wGfifthF12nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGfifthF12nD_ok : wGfifthF12nHD.ok = true ∧ wGfifthF12nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGfifthF12nHD_cols : ∀ i : Fin 24, qmWordP (wGfifthF12nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGfifthF12nHD.colsP i.val, wGfifthF12nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGfifthF12nGD_cols : ∀ i : Fin 24, qmWordP (wGfifthF12nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGfifthF12nGD.colsP i.val, wGfifthF12nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGfifthF12nHD_rows : ∀ i : Fin 24,
    fld 24 wGfifthF12nHD.rowsP i.val = rowsOf (fun j => fld 24 wGfifthF12nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGfifthF12nGD_rows : ∀ i : Fin 24,
    fld 24 wGfifthF12nGD.rowsP i.val = rowsOf (fun j => fld 24 wGfifthF12nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGfifthF12nHT_check : shortCheckF wGfifthF12nHD fifthSrcShort.flat wGfifthF12nHT = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGfifthF12nGT_check : shortCheckF wGfifthF12nGD fourthSrcShort.flat wGfifthF12nGT = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGfifthF12nT_labels : wGfifthF12nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGfifthF12nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGfifthF12nH_growth : tensorWordGrowthAll wGfifthF12nH * 64 = 4194304 := by decide

/-- The word bound of the target word. -/
theorem wGfifthF12nG_growth : tensorWordGrowthAll wGfifthF12nG * 56 = 3670016 := by decide

/-- The coordinates of the source image. -/
theorem wGfifthF12nL_actual : griessConwayEncode (rhoLocal (identWordLocal wGfifthF12nH)
    (generatedAxisGlobalTwelveRepresentative 4)) = wGfifthF12nL.real := by
  have hT := (tensorWordAll_actual wGfifthF12nH (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [wGfifthF12nH_growth]; norm_num) 1).2
  exact IdentVec.word_actual (fifthSrcVecW 64) wGfifthF12nHW wGfifthF12nH_check wGfifthF12nHD
      wGfifthF12nD_ok.1 wGfifthF12nHD_cols
    wGfifthF12nHD_rows wGfifthF12nHT wGfifthF12nHT_check _ hT _ (fifthSrcW_rep (by norm_num))

/-- The coordinates of the target image. -/
theorem wGfifthF12nW_actual : griessConwayEncode (rhoLocal (identWordLocal wGfifthF12nG)
    (generatedAxisGlobalTwelveRepresentative 3)) = wGfifthF12nW.real := by
  have hT := (tensorWordAll_actual wGfifthF12nG (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [wGfifthF12nG_growth]; norm_num) 1).2
  exact IdentVec.word_actual (fourthSrcVecW 64) wGfifthF12nGW wGfifthF12nG_check wGfifthF12nGD
      wGfifthF12nD_ok.2 wGfifthF12nGD_cols
    wGfifthF12nGD_rows wGfifthF12nGT wGfifthF12nGT_check _ hT _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
