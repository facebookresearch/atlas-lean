/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR87nTData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[8]- <-> Tenth[51]-
(record r8f:R87-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR87nTChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR87nTH : List IdentLetter := wR8fR87nTHW.map Prod.fst

/-- The target word. -/
def wR8fR87nTG : List IdentLetter := wR8fR87nTGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR87nTH`. -/
def wR8fR87nTHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.xi),
    .letter (.sign 32 0)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR87nTHPlan_word : planWord wR8fR87nTHPlan = wR8fR87nTH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR87nTHPlan_ok : planOk wR8fR87nTHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR87nTG`. -/
def wR8fR87nTGPlan : List TPlan :=
  [.letter (.qel (qmElt (13317485, false))),
    .letter (.sign 725 0),
    .run
      [(0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false),
        (1, false), (0, true), (0, true), (1, false), (0, false), (1, false), (0, false),
        (1, false), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false),
        (1, false), (0, true), (1, false), (0, false), (0, false), (1, true), (0, false),
        (1, true), (0, false), (0, false), (1, true), (0, true), (1, true), (0, true),
        (0, true), (1, true), (0, false), (0, false), (1, true), (0, true), (1, true),
        (0, true), (1, true), (0, true), (0, true), (1, true), (0, true), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, true), (0, true), (1, false),
        (0, false), (1, false), (0, false), (0, false), (1, false), (0, false),
        (1, false), (0, false), (0, false), (1, false), (0, true)]
      [.trans 1 0, .trans 0 1, .trans 0 8, .trans 2 1, .trans 1 2, .trans 1 3, .trans 1 4,
        .trans 1 6, .trans 1 8, .trans 4 2, .trans 2 0, .trans 2 1, .trans 2 4,
        .trans 2 6, .trans 2 8, .trans 8 3, .trans 3 1, .trans 3 2, .trans 3 8,
        .trans 5 4, .trans 4 1, .trans 4 3, .trans 4 5, .trans 4 7, .trans 5 1,
        .trans 5 2, .trans 5 6, .trans 5 7, .trans 6 0, .trans 6 1, .trans 6 2,
        .trans 6 3, .trans 6 8, .trans 6 9, .trans 6 10, .trans 8 7, .trans 7 0,
        .trans 7 1, .trans 7 2, .trans 7 3, .trans 7 5, .trans 7 6, .trans 7 8,
        .trans 7 9, .trans 7 10, .trans 9 8, .trans 8 0, .trans 8 1, .trans 8 3,
        .trans 8 4, .trans 8 6, .trans 8 9, .trans 8 10, .trans 10 9, .trans 9 0,
        .trans 9 1, .trans 9 3, .trans 9 7, .trans 9 8, .trans 9 10, .trans 10 1,
        .trans 10 2, .trans 10 3, .trans 10 4, .trans 10 7, .trans 10 8, .trans 10 9],
    .letter (.xi),
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
theorem wR8fR87nTGPlan_word : planWord wR8fR87nTGPlan = wR8fR87nTG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR87nTGPlan_ok : planOk wR8fR87nTGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR87nTHX : List SVec := tensorPlanF 64 wR8fR87nTHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR87nTGX : List SVec := tensorPlanF 64 wR8fR87nTGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wR8fR87nTL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR87nTH, ShortData.ofList wR8fR87nTHT, (1 / 128),
    tensorRat 64 wR8fR87nTHX ((tensorWordDenAll wR8fR87nTH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR87nTW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wR8fR87nTG, ShortData.ofList wR8fR87nTGT, (1 / 128),
    tensorRat 64 wR8fR87nTGX ((tensorWordDenAll wR8fR87nTG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR87nTH_check : wR8fR87nTHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR87nTD_ok : wR8fR87nTHD.ok = true ∧ wR8fR87nTGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR87nTHD_cols : ∀ i : Fin 24, qmWordP (wR8fR87nTHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR87nTHD.colsP i.val, wR8fR87nTHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR87nTHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR87nTHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR87nTHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR87nTHT_check : shortCheckF wR8fR87nTHD srcRootEightCShort.flat wR8fR87nTHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR87nTT_labels : wR8fR87nTHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR87nTGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR87nTH_growth : tensorWordGrowthAll wR8fR87nTH * 15 = 2013265920 := by decide

/-- The word bound of the target word. -/
theorem wR8fR87nTG_growth : tensorWordGrowthAll wR8fR87nTG * 15 = 2013265920 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR87nTL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR87nTH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR87nTL.real := by
  have hT := (tensorPlanF_actual wR8fR87nTHPlan wR8fR87nTHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR87nTHPlan_word, wR8fR87nTH_growth]; norm_num) 32).2
  rw [wR8fR87nTHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR87nTHW wR8fR87nTH_check wR8fR87nTHD
      wR8fR87nTD_ok.1 wR8fR87nTHD_cols
    wR8fR87nTHD_rows wR8fR87nTHT wR8fR87nTHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
