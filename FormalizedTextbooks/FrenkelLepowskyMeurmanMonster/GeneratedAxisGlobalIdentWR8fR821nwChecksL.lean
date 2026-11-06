/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwData
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
`GeneratedAxisGlobalIdentWR8fR821nwChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR821nwH : List IdentLetter := wR8fR821nwHW.map Prod.fst

/-- The target word. -/
def wR8fR821nwG : List IdentLetter := wR8fR821nwGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR821nwH`. -/
def wR8fR821nwHPlan : List TPlan :=
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
theorem wR8fR821nwHPlan_word : planWord wR8fR821nwHPlan = wR8fR821nwH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR821nwHPlan_ok : planOk wR8fR821nwHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR821nwG`. -/
def wR8fR821nwGPlan : List TPlan :=
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
theorem wR8fR821nwGPlan_word : planWord wR8fR821nwGPlan = wR8fR821nwG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR821nwGPlan_ok : planOk wR8fR821nwGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR821nwHX : List SVec := tensorPlanF 96 wR8fR821nwHPlan (rootEightSrcXL 96)

/-- The packed tensor of the target image. -/
def wR8fR821nwGX : List SVec := tensorPlanF 96 wR8fR821nwGPlan (rootEightSrcXL 96)

/-- The representation of the source image. -/
def wR8fR821nwL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR821nwH, ShortData.ofList wR8fR821nwHT, (1 / 128),
    tensorRat 96 wR8fR821nwHX ((tensorWordDenAll wR8fR821nwH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR821nwW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR821nwG, ShortData.ofList wR8fR821nwGT, (1 / 128),
    tensorRat 96 wR8fR821nwGX ((tensorWordDenAll wR8fR821nwG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR821nwH_check : wR8fR821nwHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR821nwD_ok : wR8fR821nwHD.ok = true ∧ wR8fR821nwGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR821nwHD_cols : ∀ i : Fin 24, qmWordP (wR8fR821nwHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR821nwHD.colsP i.val, wR8fR821nwHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR821nwHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR821nwHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR821nwHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR821nwHT_check : shortCheckF wR8fR821nwHD srcRootEightCShort.flat wR8fR821nwHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR821nwT_labels : wR8fR821nwHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR821nwGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR821nwH_growth : tensorWordGrowthAll wR8fR821nwH * 15 = 2013265920 := by decide

/-- The word bound of the target word. -/
theorem wR8fR821nwG_growth : tensorWordGrowthAll wR8fR821nwG * 15 = 16106127360 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR821nwL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR821nwH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR821nwL.real := by
  have hT := (tensorPlanF_actual wR8fR821nwHPlan wR8fR821nwHPlan_ok (rootEightSrcXL_bnd (w := 96)
      (by norm_num))
    (by rw [wR8fR821nwHPlan_word, wR8fR821nwH_growth]; norm_num) 32).2
  rw [wR8fR821nwHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 96) wR8fR821nwHW wR8fR821nwH_check wR8fR821nwHD
      wR8fR821nwD_ok.1 wR8fR821nwHD_cols
    wR8fR821nwHD_rows wR8fR821nwHT wR8fR821nwHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
