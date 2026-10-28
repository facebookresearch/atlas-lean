/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[24]+ <-> Tenth[61]+
(record goctad:E19@T33+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadE19T33pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadE19T33pH : List IdentLetter := wGoctadE19T33pHW.map Prod.fst

/-- The target word. -/
def wGoctadE19T33pG : List IdentLetter := wGoctadE19T33pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE19T33pH`. -/
def wGoctadE19T33pHPlan : List TPlan :=
  [.letter (.qel (qmElt (8443954, true))),
    .letter (.sign 1516 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, true), (1, false), (0, true), (0, true), (0, true),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, true), (0, true),
        (0, true), (1, true), (0, false), (0, false), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, true),
        (0, true), (1, true), (0, false), (1, true), (0, false), (0, false), (1, true),
        (0, true), (1, false), (0, false), (0, false), (1, false), (0, true), (1, false),
        (0, true), (0, true), (1, false), (0, true), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, true), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, false), (1, false)]
      [.trans 0 3, .trans 0 6, .trans 0 9, .trans 10 1, .trans 1 10, .trans 1 11, .trans 5 2,
        .trans 2 0, .trans 2 1, .trans 2 5, .trans 2 6, .trans 4 3, .trans 3 2,
        .trans 3 4, .trans 3 6, .trans 4 0, .trans 4 1, .trans 4 2, .trans 4 3,
        .trans 4 7, .trans 4 8, .trans 4 9, .trans 4 11, .trans 7 5, .trans 5 1,
        .trans 5 3, .trans 5 4, .trans 5 7, .trans 5 9, .trans 6 0, .trans 6 1,
        .trans 6 2, .trans 6 4, .trans 9 7, .trans 7 0, .trans 7 2, .trans 7 3,
        .trans 7 4, .trans 7 9, .trans 9 8, .trans 8 0, .trans 8 3, .trans 8 6,
        .trans 8 9, .trans 8 11, .trans 10 9, .trans 9 0, .trans 9 4, .trans 9 5,
        .trans 9 6, .trans 9 7, .trans 9 8, .trans 9 10, .trans 10 1, .trans 10 3,
        .trans 10 6, .trans 10 7, .trans 10 11],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (1, true)]
      [.trans 1 0, .trans 0 1, .trans 0 2, .trans 0 3, .trans 0 5, .trans 0 7, .trans 0 9,
        .trans 0 10, .trans 0 11, .trans 5 1, .trans 1 0, .trans 1 5, .trans 1 7,
        .trans 1 8, .trans 1 10, .trans 1 11, .trans 2 3, .trans 2 4, .trans 2 5,
        .trans 2 11, .trans 4 3, .trans 3 0, .trans 3 2, .trans 3 4, .trans 3 6,
        .trans 3 9, .trans 3 10, .trans 3 11, .trans 9 4, .trans 4 0, .trans 4 9,
        .trans 4 10, .trans 4 11, .trans 6 5, .trans 5 1, .trans 5 3, .trans 5 4,
        .trans 5 6, .trans 5 8, .trans 8 6, .trans 6 0, .trans 6 1, .trans 6 2,
        .trans 6 3, .trans 6 8, .trans 6 10, .trans 6 11, .trans 7 0, .trans 7 1,
        .trans 7 3, .trans 7 4, .trans 7 10, .trans 7 11, .trans 8 0, .trans 8 1,
        .trans 8 2, .trans 8 4, .trans 8 6, .trans 8 10, .trans 9 3, .trans 9 4,
        .trans 9 5, .trans 9 6, .trans 9 8, .trans 9 10, .trans 9 11, .trans 10 1,
        .trans 10 4, .trans 10 6],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadE19T33pHPlan_word : planWord wGoctadE19T33pHPlan = wGoctadE19T33pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE19T33pHPlan_ok : planOk wGoctadE19T33pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE19T33pG`. -/
def wGoctadE19T33pGPlan : List TPlan :=
  [.letter (.qel (qmElt (9006242, true))),
    .letter (.sign 1264 0),
    .run
      [(1, false), (0, true), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, false), (0, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, false), (0, false), (1, false), (0, true), (0, true), (1, true), (0, false),
        (0, false), (0, false), (1, true), (0, false), (0, false), (1, true), (0, true),
        (1, true), (0, true), (0, true), (1, true), (0, false), (1, true), (0, true),
        (1, true), (0, true), (1, true), (0, true), (0, true), (0, true), (0, true),
        (1, false), (0, false), (1, false), (0, false), (1, false), (0, true),
        (1, false), (0, true), (0, true), (1, false), (0, true), (0, true), (1, false),
        (0, true), (1, false), (0, false), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, false), (0, false)]
      [.trans 3 4, .trans 6 2, .trans 7 3, .trans 10 11, .trans 4 7, .trans 7 1, .trans 7 6,
        .trans 9 7, .trans 7 5, .trans 5 0, .trans 0 3, .trans 3 6, .trans 6 2,
        .trans 3 5, .trans 4 5, .trans 6 0, .trans 5 3, .trans 3 10, .trans 5 1,
        .trans 1 10, .trans 10 1, .trans 8 0, .trans 0 3, .trans 3 4, .trans 1 10,
        .trans 10 11],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true), (0, true), (0, true)]
      [.trans 0 5, .trans 8 4, .trans 2 0, .trans 4 3, .trans 4 1, .trans 9 11, .trans 4 6,
        .trans 3 9, .trans 0 4, .trans 4 2, .trans 2 10, .trans 0 11, .trans 10 7,
        .trans 6 9, .trans 6 10, .trans 10 2, .trans 6 8, .trans 9 11, .trans 8 5,
        .trans 7 5, .trans 5 7, .trans 7 11, .trans 7 0, .trans 7 1, .trans 5 10,
        .trans 1 2, .trans 5 8, .trans 2 9, .trans 2 11, .trans 10 4, .trans 0 7,
        .trans 3 4, .trans 4 0, .trans 4 7, .trans 9 7, .trans 7 9, .trans 8 0,
        .trans 8 3, .trans 8 4, .trans 8 7, .trans 8 9, .trans 9 0, .trans 9 3,
        .trans 9 4, .trans 9 8]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadE19T33pGPlan_word : planWord wGoctadE19T33pGPlan = wGoctadE19T33pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE19T33pGPlan_ok : planOk wGoctadE19T33pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadE19T33pHX : List SVec := tensorPlanF 64 wGoctadE19T33pHPlan (eighthSrcXT 64)

/-- The packed tensor of the target image. -/
def wGoctadE19T33pGX : List SVec := tensorPlanF 64 wGoctadE19T33pGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGoctadE19T33pL : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGoctadE19T33pH, ShortData.ofList wGoctadE19T33pHT, (1 /
      32),
    tensorRat 64 wGoctadE19T33pHX ((tensorWordDenAll wGoctadE19T33pH : ℚ) * (2 *
        ((tensorWordDenAll srcEighthH : ℚ) * 1)))⟩

/-- The representation of the target image. -/
def wGoctadE19T33pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGoctadE19T33pG, ShortData.ofList wGoctadE19T33pGT, (1 /
      128),
    tensorRat 64 wGoctadE19T33pGX ((tensorWordDenAll wGoctadE19T33pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadE19T33pH_check : wGoctadE19T33pHW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadE19T33pD_ok : wGoctadE19T33pHD.ok = true ∧ wGoctadE19T33pGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadE19T33pHD_cols : ∀ i : Fin 24, qmWordP (wGoctadE19T33pHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGoctadE19T33pHD.colsP i.val, wGoctadE19T33pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadE19T33pHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE19T33pHD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE19T33pHD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadE19T33pHT_check : shortCheckF wGoctadE19T33pHD eighthShS.flat wGoctadE19T33pHT =
    true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadE19T33pT_labels : wGoctadE19T33pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGoctadE19T33pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadE19T33pH_growth : tensorWordGrowthAll wGoctadE19T33pH * (2 ^ 13 - 1) =
    281440616972288 := by decide

/-- The word bound of the target word. -/
theorem wGoctadE19T33pG_growth : tensorWordGrowthAll wGoctadE19T33pG * 15 = 515396075520 := by
    decide

/-- The coordinates of the source image. -/
theorem wGoctadE19T33pL_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE19T33pH)
    (generatedAxisGlobalTwelveRepresentative 7)) = wGoctadE19T33pL.real := by
  have hT := (tensorPlanF_actual wGoctadE19T33pHPlan wGoctadE19T33pHPlan_ok (eighthSrcXT_bnd (w :=
      64) (by norm_num))
    (by rw [wGoctadE19T33pHPlan_word, wGoctadE19T33pH_growth]; norm_num) (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1))).2
  rw [wGoctadE19T33pHPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 64) wGoctadE19T33pHW wGoctadE19T33pH_check
      wGoctadE19T33pHD wGoctadE19T33pD_ok.1 wGoctadE19T33pHD_cols
    wGoctadE19T33pHD_rows wGoctadE19T33pHT wGoctadE19T33pHT_check _ hT _ (eighthSrcT_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
