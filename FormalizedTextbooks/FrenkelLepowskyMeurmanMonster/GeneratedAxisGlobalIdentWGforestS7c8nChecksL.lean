/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[13]+ <-> Seventh[14]-
(record gforest:S7c8-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGforestS7c8nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGforestS7c8nH : List IdentLetter := wGforestS7c8nHW.map Prod.fst

/-- The target word. -/
def wGforestS7c8nG : List IdentLetter := wGforestS7c8nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGforestS7c8nH`. -/
def wGforestS7c8nHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(1, true), (0, true)]
      [.trans 9 5, .trans 6 1, .trans 10 6, .trans 8 7, .trans 10 4, .trans 0 6, .trans 0 11,
        .trans 7 2, .trans 2 9, .trans 2 8, .trans 8 10, .trans 6 0, .trans 6 9,
        .trans 4 7, .trans 7 8, .trans 5 8, .trans 8 5, .trans 0 10, .trans 9 10,
        .trans 0 3, .trans 5 3, .trans 10 2, .trans 0 6, .trans 10 3, .trans 3 11,
        .trans 3 5, .trans 5 0, .trans 5 1, .trans 1 4, .trans 1 11, .trans 0 8,
        .trans 0 9, .trans 0 11, .trans 2 7, .trans 2 11, .trans 4 2, .trans 4 7,
        .trans 4 11, .trans 7 0, .trans 7 6, .trans 7 8, .trans 7 9, .trans 7 11,
        .trans 8 2, .trans 8 4, .trans 8 11],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, false)]
      [.trans 10 11, .trans 0 10, .trans 1 6, .trans 4 1, .trans 1 0, .trans 10 4, .trans 4 3,
        .trans 1 2, .trans 9 10, .trans 6 0, .trans 0 5, .trans 4 6, .trans 6 1,
        .trans 7 1, .trans 2 1, .trans 1 4, .trans 10 11, .trans 0 7, .trans 3 6,
        .trans 1 8, .trans 8 3, .trans 8 9, .trans 9 2, .trans 2 9, .trans 9 2,
        .trans 0 11, .trans 3 8, .trans 4 5, .trans 5 0, .trans 5 9, .trans 5 11,
        .trans 6 0, .trans 6 7, .trans 6 11, .trans 7 3, .trans 7 8, .trans 8 3,
        .trans 8 4, .trans 8 5, .trans 8 6, .trans 8 7, .trans 8 9]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGforestS7c8nHPlan_word : planWord wGforestS7c8nHPlan = wGforestS7c8nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGforestS7c8nHPlan_ok : planOk wGforestS7c8nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGforestS7c8nG`. -/
def wGforestS7c8nGPlan : List TPlan :=
  [.letter (.qel (qmElt (9686450, true))),
    .letter (.sign 1422 0),
    .run
      [(0, true), (1, false), (0, true), (0, true), (1, false), (0, true), (1, false),
        (0, false), (0, false), (1, false), (0, true), (1, false), (0, false),
        (1, false), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, false), (0, false),
        (0, false), (1, true), (0, true), (0, true), (1, true), (0, true), (1, true),
        (0, true), (0, true), (1, true), (0, true), (0, true), (1, true), (0, false),
        (0, false), (1, true), (0, false), (0, false), (0, false), (0, false),
        (1, false), (0, false), (1, false), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, true), (0, true), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, false), (1, false), (0, false), (1, false)]
      [.trans 10 8, .trans 10 4, .trans 3 7, .trans 6 10, .trans 11 1, .trans 5 11, .trans 5 4,
        .trans 4 10, .trans 10 4, .trans 10 11, .trans 10 9, .trans 9 2, .trans 9 6,
        .trans 4 0, .trans 1 5, .trans 2 8, .trans 8 2, .trans 8 3, .trans 0 6,
        .trans 6 3, .trans 6 9, .trans 5 1, .trans 3 11, .trans 3 7, .trans 11 5,
        .trans 5 0, .trans 0 5, .trans 0 8, .trans 0 1, .trans 1 7, .trans 7 9,
        .trans 9 6],
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
theorem wGforestS7c8nGPlan_word : planWord wGforestS7c8nGPlan = wGforestS7c8nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGforestS7c8nGPlan_ok : planOk wGforestS7c8nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGforestS7c8nHX : List SVec := tensorPlanF 72 wGforestS7c8nHPlan (srcSeventhX0F 72)

/-- The packed tensor of the target image. -/
def wGforestS7c8nGX : List SVec := tensorPlanF 72 wGforestS7c8nGPlan (eighthSrcXT 72)

/-- The representation of the source image. -/
def wGforestS7c8nL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet wGforestS7c8nH, ShortData.ofList wGforestS7c8nHT, (1 /
      32),
    tensorRat 72 wGforestS7c8nHX ((tensorWordDenAll wGforestS7c8nH : ℚ) * srcSeventhD0)⟩

/-- The representation of the target image. -/
def wGforestS7c8nW : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGforestS7c8nG, ShortData.ofList wGforestS7c8nGT, (1 / 32),
    tensorRat 72 wGforestS7c8nGX ((tensorWordDenAll wGforestS7c8nG : ℚ) * (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1)))⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGforestS7c8nH_check : wGforestS7c8nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGforestS7c8nD_ok : wGforestS7c8nHD.ok = true ∧ wGforestS7c8nGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGforestS7c8nHD_cols : ∀ i : Fin 24, qmWordP (wGforestS7c8nHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS7c8nHD.colsP i.val, wGforestS7c8nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGforestS7c8nHD_rows : ∀ i : Fin 24,
    fld 24 wGforestS7c8nHD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS7c8nHD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGforestS7c8nHT_check : shortCheckF wGforestS7c8nHD seventhShS.flat wGforestS7c8nHT = true
    :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGforestS7c8nT_labels : wGforestS7c8nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGforestS7c8nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGforestS7c8nH_growth : tensorWordGrowthAll wGforestS7c8nH * (4 * (16777216 * 8) + 276 *
    6144) = 9035649118109696 := by decide

/-- The word bound of the target word. -/
theorem wGforestS7c8nG_growth : tensorWordGrowthAll wGforestS7c8nG * (2 ^ 13 - 1) =
    18444492273895866368 := by decide

/-- The coordinates of the source image. -/
theorem wGforestS7c8nL_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS7c8nH)
    (generatedAxisGlobalTwelveRepresentative 6)) = wGforestS7c8nL.real := by
  have hT := (tensorPlanF_actual wGforestS7c8nHPlan wGforestS7c8nHPlan_ok (srcSeventhX0F_bnd (w :=
      72) (by norm_num))
    (by rw [wGforestS7c8nHPlan_word, wGforestS7c8nH_growth]; norm_num) srcSeventhD0).2
  rw [wGforestS7c8nHPlan_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 72) wGforestS7c8nHW wGforestS7c8nH_check
      wGforestS7c8nHD wGforestS7c8nD_ok.1 wGforestS7c8nHD_cols
    wGforestS7c8nHD_rows wGforestS7c8nHT wGforestS7c8nHT_check _ hT _ (seventhSrcS_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
