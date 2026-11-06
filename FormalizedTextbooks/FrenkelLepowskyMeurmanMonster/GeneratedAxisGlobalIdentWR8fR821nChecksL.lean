/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[33]- <-> Root8[33]-
(record r8f:R821-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR821nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR821nH : List IdentLetter := wR8fR821nHW.map Prod.fst

/-- The target word. -/
def wR8fR821nG : List IdentLetter := wR8fR821nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR821nH`. -/
def wR8fR821nHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true)]
      [.trans 3 11, .trans 7 6, .trans 4 5, .trans 11 2, .trans 10 3, .trans 4 1, .trans 1 8,
        .trans 9 7, .trans 6 10, .trans 10 9, .trans 3 7, .trans 6 2, .trans 10 11,
        .trans 7 4, .trans 11 4, .trans 10 8, .trans 5 1, .trans 1 9, .trans 4 2,
        .trans 2 3, .trans 9 11, .trans 8 0, .trans 2 0, .trans 5 6, .trans 7 9,
        .trans 9 8, .trans 8 3, .trans 8 11, .trans 8 10, .trans 8 7, .trans 0 5,
        .trans 1 0, .trans 1 5, .trans 3 4, .trans 4 2, .trans 4 7, .trans 4 9,
        .trans 5 6, .trans 5 11, .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 3,
        .trans 6 4, .trans 6 7, .trans 6 9, .trans 9 10, .trans 11 2, .trans 11 4,
        .trans 11 7, .trans 11 9, .trans 11 10],
    .letter (.xi),
    .letter (.sign 16 0)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR821nHPlan_word : planWord wR8fR821nHPlan = wR8fR821nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR821nHPlan_ok : planOk wR8fR821nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR821nG`. -/
def wR8fR821nGPlan : List TPlan :=
  [.letter (.qel (qmElt (9818112, false))),
    .letter (.sign 1778 0),
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true)]
      [.trans 3 11, .trans 7 6, .trans 4 5, .trans 11 2, .trans 10 3, .trans 4 1, .trans 1 8,
        .trans 9 7, .trans 6 10, .trans 10 9, .trans 3 7, .trans 6 2, .trans 10 11,
        .trans 7 4, .trans 11 4, .trans 10 8, .trans 5 1, .trans 1 9, .trans 4 2,
        .trans 2 3, .trans 9 11, .trans 8 0, .trans 2 0, .trans 5 6, .trans 7 9,
        .trans 9 8, .trans 8 3, .trans 8 11, .trans 8 10, .trans 8 7, .trans 0 5,
        .trans 1 0, .trans 1 5, .trans 3 4, .trans 4 2, .trans 4 7, .trans 4 9,
        .trans 5 6, .trans 5 11, .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 3,
        .trans 6 4, .trans 6 7, .trans 6 9, .trans 9 10, .trans 11 2, .trans 11 4,
        .trans 11 7, .trans 11 9, .trans 11 10],
    .letter (.xi),
    .letter (.sign 16 0)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR821nGPlan_word : planWord wR8fR821nGPlan = wR8fR821nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR821nGPlan_ok : planOk wR8fR821nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR821nHX : List SVec := tensorPlanF 64 wR8fR821nHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR821nGX : List SVec := tensorPlanF 64 wR8fR821nGPlan (rootEightSrcXL 64)

/-- The representation of the source image. -/
def wR8fR821nL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR821nH, ShortData.ofList wR8fR821nHT, (1 / 128),
    tensorRat 64 wR8fR821nHX ((tensorWordDenAll wR8fR821nH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR821nW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR821nG, ShortData.ofList wR8fR821nGT, (1 / 128),
    tensorRat 64 wR8fR821nGX ((tensorWordDenAll wR8fR821nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR821nH_check : wR8fR821nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR821nD_ok : wR8fR821nHD.ok = true ∧ wR8fR821nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR821nHD_cols : ∀ i : Fin 24, qmWordP (wR8fR821nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR821nHD.colsP i.val, wR8fR821nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR821nHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR821nHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR821nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR821nHT_check : shortCheckF wR8fR821nHD srcRootEightCShort.flat wR8fR821nHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR821nT_labels : wR8fR821nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR821nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR821nH_growth : tensorWordGrowthAll wR8fR821nH * 15 = 2013265920 := by decide

/-- The word bound of the target word. -/
theorem wR8fR821nG_growth : tensorWordGrowthAll wR8fR821nG * 15 = 16106127360 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR821nL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR821nH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR821nL.real := by
  have hT := (tensorPlanF_actual wR8fR821nHPlan wR8fR821nHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR821nHPlan_word, wR8fR821nH_growth]; norm_num) 32).2
  rw [wR8fR821nHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR821nHW wR8fR821nH_check wR8fR821nHD
      wR8fR821nD_ok.1 wR8fR821nHD_cols
    wR8fR821nHD_rows wR8fR821nHT wR8fR821nHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
