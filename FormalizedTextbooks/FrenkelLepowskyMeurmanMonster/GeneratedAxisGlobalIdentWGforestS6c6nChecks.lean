/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c6nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixth

/-! # Factory checks of the identification Sixth[11]- <-> Sixth[11]- (record gforest:S6c6-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words) and bound to the genuine coordinates of the two local images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGforestS6c6nH : List IdentLetter := wGforestS6c6nHW.map Prod.fst

/-- The target word. -/
def wGforestS6c6nG : List IdentLetter := wGforestS6c6nGW.map Prod.fst

/-- The packed tensor of the source image. -/
def wGforestS6c6nHX : List SVec := tensorWordAll 64 wGforestS6c6nH (sixthSrcXW 64)

/-- The packed tensor of the target image. -/
def wGforestS6c6nGX : List SVec := tensorWordAll 64 wGforestS6c6nG (sixthSrcXW 64)

/-- The representation of the source image. -/
def wGforestS6c6nL : IdentVec :=
  ⟨sixthSrcMat.act identSpatialAlphabet wGforestS6c6nH, ShortData.ofList wGforestS6c6nHT, 1 / 32,
    tensorRat 64 wGforestS6c6nHX ((tensorWordDenAll wGforestS6c6nH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGforestS6c6nW : IdentVec :=
  ⟨sixthSrcMat.act identSpatialAlphabet wGforestS6c6nG, ShortData.ofList wGforestS6c6nGT, 1 / 32,
    tensorRat 64 wGforestS6c6nGX ((tensorWordDenAll wGforestS6c6nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGforestS6c6nH_check : wGforestS6c6nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGforestS6c6nG_check : wGforestS6c6nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGforestS6c6nD_ok : wGforestS6c6nHD.ok = true ∧ wGforestS6c6nGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGforestS6c6nHD_cols : ∀ i : Fin 24, qmWordP (wGforestS6c6nHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS6c6nHD.colsP i.val, wGforestS6c6nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGforestS6c6nGD_cols : ∀ i : Fin 24, qmWordP (wGforestS6c6nGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS6c6nGD.colsP i.val, wGforestS6c6nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGforestS6c6nHD_rows : ∀ i : Fin 24,
    fld 24 wGforestS6c6nHD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS6c6nHD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGforestS6c6nGD_rows : ∀ i : Fin 24,
    fld 24 wGforestS6c6nGD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS6c6nGD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGforestS6c6nHT_check : shortCheckF wGforestS6c6nHD sixthLitShort.flat wGforestS6c6nHT =
    true :=
  shortCheckPk_sound _ 10 30 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGforestS6c6nGT_check : shortCheckF wGforestS6c6nGD sixthLitShort.flat wGforestS6c6nGT =
    true :=
  shortCheckPk_sound _ 10 30 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGforestS6c6nT_labels : wGforestS6c6nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGforestS6c6nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGforestS6c6nH_growth : tensorWordGrowthAll wGforestS6c6nH * 262144 = 1125899906842624 :=
    by decide

/-- The word bound of the target word. -/
theorem wGforestS6c6nG_growth : tensorWordGrowthAll wGforestS6c6nG * 262144 = 9007199254740992 :=
    by decide

/-- The coordinates of the source image. -/
theorem wGforestS6c6nL_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS6c6nH)
    (generatedAxisGlobalTwelveRepresentative 5)) = wGforestS6c6nL.real := by
  have hT := (tensorWordAll_actual wGforestS6c6nH (sixthSrcXW_bndN (w := 64) (by norm_num))
    (by rw [wGforestS6c6nH_growth]; norm_num) 32).2
  exact IdentVec.word_actual (sixthSrcVecL 64) wGforestS6c6nHW wGforestS6c6nH_check
      wGforestS6c6nHD wGforestS6c6nD_ok.1 wGforestS6c6nHD_cols
    wGforestS6c6nHD_rows wGforestS6c6nHT wGforestS6c6nHT_check _ hT _ (sixthSrcL_rep (by norm_num))

/-- The coordinates of the target image. -/
theorem wGforestS6c6nW_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS6c6nG)
    (generatedAxisGlobalTwelveRepresentative 5)) = wGforestS6c6nW.real := by
  have hT := (tensorWordAll_actual wGforestS6c6nG (sixthSrcXW_bndN (w := 64) (by norm_num))
    (by rw [wGforestS6c6nG_growth]; norm_num) 32).2
  exact IdentVec.word_actual (sixthSrcVecL 64) wGforestS6c6nGW wGforestS6c6nG_check
      wGforestS6c6nGD wGforestS6c6nD_ok.2 wGforestS6c6nGD_cols
    wGforestS6c6nGD_rows wGforestS6c6nGT wGforestS6c6nGT_check _ hT _ (sixthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
