/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82pTData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[18]- <-> Root8[2]+
(record r8f:R82+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR82pTChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR82pTH : List IdentLetter := wR8fR82pTHW.map Prod.fst

/-- The target word. -/
def wR8fR82pTG : List IdentLetter := wR8fR82pTGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR82pTH`. -/
def wR8fR82pTHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR82pTHPlan_word : planWord wR8fR82pTHPlan = wR8fR82pTH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR82pTHPlan_ok : planOk wR8fR82pTHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR82pTG`. -/
def wR8fR82pTGPlan : List TPlan :=
  [.letter (.qel (qmElt (6713675, true))),
    .letter (.sign 1702 0),
    .run
      [(0, true), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, true), (1, false),
        (0, false), (0, false), (1, true), (0, false), (1, true), (0, true), (1, true),
        (0, false), (0, false), (0, false), (1, true), (0, false), (0, false), (1, true),
        (0, false), (1, true), (0, false), (0, false), (0, false), (1, true), (0, true),
        (1, false), (0, false), (1, false), (0, false), (1, false), (0, true),
        (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, true), (1, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false)]
      [.trans 7 8, .trans 5 6, .trans 1 11, .trans 4 0, .trans 6 4, .trans 2 3, .trans 4 7,
        .trans 7 5, .trans 1 2, .trans 6 1, .trans 9 1, .trans 5 9, .trans 6 5,
        .trans 2 5, .trans 2 10, .trans 0 7, .trans 9 4, .trans 10 0, .trans 4 0,
        .trans 5 8, .trans 5 6, .trans 0 8, .trans 8 11, .trans 8 0, .trans 4 10,
        .trans 10 3, .trans 1 7, .trans 0 8, .trans 7 2, .trans 7 11, .trans 2 7,
        .trans 6 2, .trans 6 7, .trans 10 7, .trans 7 10, .trans 10 2, .trans 10 6],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi),
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR82pTGPlan_word : planWord wR8fR82pTGPlan = wR8fR82pTG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR82pTGPlan_ok : planOk wR8fR82pTGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR82pTHX : List SVec := tensorPlanF 64 wR8fR82pTHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR82pTGX : List SVec := tensorPlanF 64 wR8fR82pTGPlan (eighthSrcXT 64)

/-- The representation of the source image. -/
def wR8fR82pTL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR82pTH, ShortData.ofList wR8fR82pTHT, (1 / 128),
    tensorRat 64 wR8fR82pTHX ((tensorWordDenAll wR8fR82pTH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR82pTW : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wR8fR82pTG, ShortData.ofList wR8fR82pTGT, (1 / 32),
    tensorRat 64 wR8fR82pTGX ((tensorWordDenAll wR8fR82pTG : ℚ) * (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1)))⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR82pTH_check : wR8fR82pTHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR82pTD_ok : wR8fR82pTHD.ok = true ∧ wR8fR82pTGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR82pTHD_cols : ∀ i : Fin 24, qmWordP (wR8fR82pTHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR82pTHD.colsP i.val, wR8fR82pTHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR82pTHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR82pTHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR82pTHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR82pTHT_check : shortCheckF wR8fR82pTHD srcRootEightCShort.flat wR8fR82pTHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR82pTT_labels : wR8fR82pTHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR82pTGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR82pTH_growth : tensorWordGrowthAll wR8fR82pTH * 15 = 251658240 := by decide

/-- The word bound of the target word. -/
theorem wR8fR82pTG_growth : tensorWordGrowthAll wR8fR82pTG * (2 ^ 13 - 1) = 72048797944905728 :=
    by decide

/-- The coordinates of the source image. -/
theorem wR8fR82pTL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR82pTH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR82pTL.real := by
  have hT := (tensorPlanF_actual wR8fR82pTHPlan wR8fR82pTHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR82pTHPlan_word, wR8fR82pTH_growth]; norm_num) 32).2
  rw [wR8fR82pTHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR82pTHW wR8fR82pTH_check wR8fR82pTHD
      wR8fR82pTD_ok.1 wR8fR82pTHD_cols
    wR8fR82pTHD_rows wR8fR82pTHT wR8fR82pTHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
