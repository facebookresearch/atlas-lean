/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[27]+ <-> Seventh[22]+
(record gforest:S7c14+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGforestS7c14pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGforestS7c14pH : List IdentLetter := wGforestS7c14pHW.map Prod.fst

/-- The target word. -/
def wGforestS7c14pG : List IdentLetter := wGforestS7c14pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGforestS7c14pH`. -/
def wGforestS7c14pHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
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
        .trans 10 4, .trans 10 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGforestS7c14pHPlan_word : planWord wGforestS7c14pHPlan = wGforestS7c14pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGforestS7c14pHPlan_ok : planOk wGforestS7c14pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGforestS7c14pG`. -/
def wGforestS7c14pGPlan : List TPlan :=
  [.letter (.qel (qmElt (725440, false))),
    .letter (.sign 1366 0),
    .run
      [(1, false), (0, false), (1, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, true), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (1, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, false), (1, true), (0, true), (0, true), (1, true),
        (0, false), (0, false), (0, false), (1, true), (0, true), (0, true), (0, true),
        (1, true), (0, true), (0, true), (0, true), (1, true), (0, true), (1, false),
        (0, false), (1, false), (0, true), (1, false), (0, true), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, false), (0, false), (1, false), (0, false), (0, false), (1, false),
        (0, false)]
      [.trans 3 0, .trans 3 5, .trans 2 4, .trans 4 7, .trans 10 1, .trans 3 11, .trans 9 10,
        .trans 9 8, .trans 1 3, .trans 2 9, .trans 6 9, .trans 9 8, .trans 8 10,
        .trans 3 2, .trans 2 1, .trans 0 7, .trans 5 4, .trans 8 4, .trans 1 7,
        .trans 0 6, .trans 6 10, .trans 6 5, .trans 7 5, .trans 0 2, .trans 2 11,
        .trans 10 3, .trans 4 9, .trans 7 8, .trans 9 5, .trans 5 6],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (1, true), (0, true)]
      [.trans 6 5, .trans 10 1, .trans 4 7, .trans 4 10, .trans 3 4, .trans 10 2, .trans 5 3,
        .trans 9 6, .trans 8 6, .trans 0 5, .trans 0 2, .trans 2 11, .trans 5 1,
        .trans 5 8, .trans 8 9, .trans 9 4, .trans 4 9, .trans 4 7, .trans 4 10,
        .trans 3 0, .trans 0 3, .trans 1 2, .trans 2 4, .trans 7 3, .trans 3 7,
        .trans 3 8, .trans 3 9, .trans 3 11, .trans 6 4, .trans 4 6, .trans 4 8,
        .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 10, .trans 7 0, .trans 10 4,
        .trans 10 8, .trans 10 11],
    .letter (.xi),
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGforestS7c14pGPlan_word : planWord wGforestS7c14pGPlan = wGforestS7c14pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGforestS7c14pGPlan_ok : planOk wGforestS7c14pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGforestS7c14pHX : List SVec := tensorPlanF 64 wGforestS7c14pHPlan (srcSeventhX0F 64)

/-- The packed tensor of the target image. -/
def wGforestS7c14pGX : List SVec := tensorPlanF 64 wGforestS7c14pGPlan (eighthSrcXT 64)

/-- The representation of the source image. -/
def wGforestS7c14pL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet wGforestS7c14pH, ShortData.ofList wGforestS7c14pHT, (1 /
      32),
    tensorRat 64 wGforestS7c14pHX ((tensorWordDenAll wGforestS7c14pH : ℚ) * srcSeventhD0)⟩

/-- The representation of the target image. -/
def wGforestS7c14pW : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGforestS7c14pG, ShortData.ofList wGforestS7c14pGT, (1 /
      32),
    tensorRat 64 wGforestS7c14pGX ((tensorWordDenAll wGforestS7c14pG : ℚ) * (2 *
        ((tensorWordDenAll srcEighthH : ℚ) * 1)))⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGforestS7c14pH_check : wGforestS7c14pHW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGforestS7c14pD_ok : wGforestS7c14pHD.ok = true ∧ wGforestS7c14pGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGforestS7c14pHD_cols : ∀ i : Fin 24, qmWordP (wGforestS7c14pHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS7c14pHD.colsP i.val, wGforestS7c14pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGforestS7c14pHD_rows : ∀ i : Fin 24,
    fld 24 wGforestS7c14pHD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS7c14pHD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGforestS7c14pHT_check : shortCheckF wGforestS7c14pHD seventhShS.flat wGforestS7c14pHT =
    true :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGforestS7c14pT_labels : wGforestS7c14pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGforestS7c14pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGforestS7c14pH_growth : tensorWordGrowthAll wGforestS7c14pH * (4 * (16777216 * 8) + 276 *
    6144) = 9035649118109696 := by decide

/-- The word bound of the target word. -/
theorem wGforestS7c14pG_growth : tensorWordGrowthAll wGforestS7c14pG * (2 ^ 13 - 1) =
    281440616972288 := by decide

/-- The coordinates of the source image. -/
theorem wGforestS7c14pL_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS7c14pH)
    (generatedAxisGlobalTwelveRepresentative 6)) = wGforestS7c14pL.real := by
  have hT := (tensorPlanF_actual wGforestS7c14pHPlan wGforestS7c14pHPlan_ok (srcSeventhX0F_bnd (w
      := 64) (by norm_num))
    (by rw [wGforestS7c14pHPlan_word, wGforestS7c14pH_growth]; norm_num) srcSeventhD0).2
  rw [wGforestS7c14pHPlan_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 64) wGforestS7c14pHW wGforestS7c14pH_check
      wGforestS7c14pHD wGforestS7c14pD_ok.1 wGforestS7c14pHD_cols
    wGforestS7c14pHD_rows wGforestS7c14pHT wGforestS7c14pHT_check _ hT _ (seventhSrcS_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
