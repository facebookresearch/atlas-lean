/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGfifthF0nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW

/-! # Factory checks of the identification Fifth[0]- <-> Fifth[0]- (record gfifth:F0-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words) and bound to the genuine coordinates of the two local images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGfifthF0nH : List IdentLetter := wGfifthF0nHW.map Prod.fst

/-- The target word. -/
def wGfifthF0nG : List IdentLetter := wGfifthF0nGW.map Prod.fst

/-- The packed tensor of the source image. -/
def wGfifthF0nHX : List SVec := tensorWordAll 64 wGfifthF0nH (fifthSrcXW 64)

/-- The packed tensor of the target image. -/
def wGfifthF0nGX : List SVec := tensorWordAll 64 wGfifthF0nG (fifthSrcXW 64)

/-- The representation of the source image. -/
def wGfifthF0nL : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet wGfifthF0nH, ShortData.ofList wGfifthF0nHT, 1 / 16,
    tensorRat 64 wGfifthF0nHX ((tensorWordDenAll wGfifthF0nH : ℚ) * 1)⟩

/-- The representation of the target image. -/
def wGfifthF0nW : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet wGfifthF0nG, ShortData.ofList wGfifthF0nGT, 1 / 16,
    tensorRat 64 wGfifthF0nGX ((tensorWordDenAll wGfifthF0nG : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGfifthF0nH_check : wGfifthF0nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGfifthF0nG_check : wGfifthF0nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGfifthF0nD_ok : wGfifthF0nHD.ok = true ∧ wGfifthF0nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGfifthF0nHD_cols : ∀ i : Fin 24, qmWordP (wGfifthF0nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGfifthF0nHD.colsP i.val, wGfifthF0nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGfifthF0nGD_cols : ∀ i : Fin 24, qmWordP (wGfifthF0nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGfifthF0nGD.colsP i.val, wGfifthF0nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGfifthF0nHD_rows : ∀ i : Fin 24,
    fld 24 wGfifthF0nHD.rowsP i.val = rowsOf (fun j => fld 24 wGfifthF0nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGfifthF0nGD_rows : ∀ i : Fin 24,
    fld 24 wGfifthF0nGD.rowsP i.val = rowsOf (fun j => fld 24 wGfifthF0nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGfifthF0nHT_check : shortCheckF wGfifthF0nHD fifthSrcShort.flat wGfifthF0nHT = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGfifthF0nGT_check : shortCheckF wGfifthF0nGD fifthSrcShort.flat wGfifthF0nGT = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGfifthF0nT_labels : wGfifthF0nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGfifthF0nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGfifthF0nH_growth : tensorWordGrowthAll wGfifthF0nH * 64 = 4194304 := by decide

/-- The word bound of the target word. -/
theorem wGfifthF0nG_growth : tensorWordGrowthAll wGfifthF0nG * 64 = 33554432 := by decide

/-- The coordinates of the source image. -/
theorem wGfifthF0nL_actual : griessConwayEncode (rhoLocal (identWordLocal wGfifthF0nH)
    (generatedAxisGlobalTwelveRepresentative 4)) = wGfifthF0nL.real := by
  have hT := (tensorWordAll_actual wGfifthF0nH (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [wGfifthF0nH_growth]; norm_num) 1).2
  exact IdentVec.word_actual (fifthSrcVecW 64) wGfifthF0nHW wGfifthF0nH_check wGfifthF0nHD
      wGfifthF0nD_ok.1 wGfifthF0nHD_cols
    wGfifthF0nHD_rows wGfifthF0nHT wGfifthF0nHT_check _ hT _ (fifthSrcW_rep (by norm_num))

/-- The coordinates of the target image. -/
theorem wGfifthF0nW_actual : griessConwayEncode (rhoLocal (identWordLocal wGfifthF0nG)
    (generatedAxisGlobalTwelveRepresentative 4)) = wGfifthF0nW.real := by
  have hT := (tensorWordAll_actual wGfifthF0nG (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [wGfifthF0nG_growth]; norm_num) 1).2
  exact IdentVec.word_actual (fifthSrcVecW 64) wGfifthF0nGW wGfifthF0nG_check wGfifthF0nGD
      wGfifthF0nD_ok.2 wGfifthF0nGD_cols
    wGfifthF0nGD_rows wGfifthF0nGT wGfifthF0nGT_check _ hT _ (fifthSrcW_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
