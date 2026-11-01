/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[13]+ <-> Seventh[14]+
(record goctad:E9+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadE9pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadE9pH : List IdentLetter := wGoctadE9pHW.map Prod.fst

/-- The target word. -/
def wGoctadE9pG : List IdentLetter := wGoctadE9pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE9pH`. -/
def wGoctadE9pHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(0, false), (1, false)]
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
    .run
      [(0, false), (1, false)]
      [.trans 3 11, .trans 7 6, .trans 4 5, .trans 11 2, .trans 10 3, .trans 4 1, .trans 1 8,
        .trans 9 7, .trans 6 10, .trans 10 9, .trans 3 7, .trans 6 2, .trans 10 11,
        .trans 7 4, .trans 11 4, .trans 10 8, .trans 5 1, .trans 1 9, .trans 4 2,
        .trans 2 3, .trans 9 11, .trans 8 0, .trans 2 0, .trans 5 6, .trans 7 9,
        .trans 9 8, .trans 8 3, .trans 8 11, .trans 8 10, .trans 8 7, .trans 0 5,
        .trans 1 0, .trans 1 5, .trans 3 4, .trans 4 2, .trans 4 7, .trans 4 9,
        .trans 5 6, .trans 5 11, .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 3,
        .trans 6 4, .trans 6 7, .trans 6 9, .trans 9 10, .trans 11 2, .trans 11 4,
        .trans 11 7, .trans 11 9, .trans 11 10]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadE9pHPlan_word : planWord wGoctadE9pHPlan = wGoctadE9pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE9pHPlan_ok : planOk wGoctadE9pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE9pG`. -/
def wGoctadE9pGPlan : List TPlan :=
  [.letter (.qel (qmElt (10510004, false))),
    .letter (.sign 243 0),
    .run
      [(1, false), (0, false), (1, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, true), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (1, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, false), (1, true), (0, true), (0, true), (1, true),
        (0, false), (0, false), (0, false), (1, true), (0, true), (0, true), (0, true),
        (1, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false),
        (1, false), (0, true), (0, true), (1, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, true), (0, true), (0, true),
        (1, false), (0, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, false), (0, false)]
      [.trans 0 2, .trans 0 3, .trans 0 4, .trans 0 5, .trans 0 8, .trans 0 9, .trans 2 1,
        .trans 1 0, .trans 1 2, .trans 1 3, .trans 1 4, .trans 1 5, .trans 1 8,
        .trans 1 9, .trans 6 2, .trans 2 0, .trans 2 1, .trans 2 6, .trans 2 7,
        .trans 4 3, .trans 3 0, .trans 3 2, .trans 3 4, .trans 3 5, .trans 3 8,
        .trans 3 9, .trans 4 0, .trans 4 1, .trans 4 2, .trans 4 9, .trans 4 10,
        .trans 6 5, .trans 5 0, .trans 5 2, .trans 5 3, .trans 5 4, .trans 5 6,
        .trans 5 8, .trans 5 9, .trans 8 6, .trans 6 0, .trans 6 1, .trans 6 5,
        .trans 6 8, .trans 6 9, .trans 7 0, .trans 7 3, .trans 7 5, .trans 10 8,
        .trans 8 1, .trans 8 2, .trans 8 5, .trans 8 10, .trans 10 9, .trans 9 3,
        .trans 9 4, .trans 9 5, .trans 9 7, .trans 9 8, .trans 9 10, .trans 10 2,
        .trans 10 4, .trans 10 5, .trans 10 6],
    .letter (.xi),
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
theorem wGoctadE9pGPlan_word : planWord wGoctadE9pGPlan = wGoctadE9pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE9pGPlan_ok : planOk wGoctadE9pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadE9pHX : List SVec := tensorPlanF 64 wGoctadE9pHPlan (eighthSrcXT 64)

/-- The packed tensor of the target image. -/
def wGoctadE9pGX : List SVec := tensorPlanF 64 wGoctadE9pGPlan (srcSeventhX0F 64)

/-- The representation of the source image. -/
def wGoctadE9pL : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGoctadE9pH, ShortData.ofList wGoctadE9pHT, (1 / 32),
    tensorRat 64 wGoctadE9pHX ((tensorWordDenAll wGoctadE9pH : ℚ) * (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1)))⟩

/-- The representation of the target image. -/
def wGoctadE9pW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet wGoctadE9pG, ShortData.ofList wGoctadE9pGT, (1 / 32),
    tensorRat 64 wGoctadE9pGX ((tensorWordDenAll wGoctadE9pG : ℚ) * srcSeventhD0)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadE9pH_check : wGoctadE9pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadE9pD_ok : wGoctadE9pHD.ok = true ∧ wGoctadE9pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadE9pHD_cols : ∀ i : Fin 24, qmWordP (wGoctadE9pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGoctadE9pHD.colsP i.val, wGoctadE9pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadE9pHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE9pHD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE9pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadE9pHT_check : shortCheckF wGoctadE9pHD eighthShS.flat wGoctadE9pHT = true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadE9pT_labels : wGoctadE9pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGoctadE9pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadE9pH_growth : tensorWordGrowthAll wGoctadE9pH * (2 ^ 13 - 1) = 536805376 := by decide

/-- The word bound of the target word. -/
theorem wGoctadE9pG_growth : tensorWordGrowthAll wGoctadE9pG * (4 * (16777216 * 8) + 276 * 6144) =
    72285192944877568 := by decide

/-- The coordinates of the source image. -/
theorem wGoctadE9pL_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE9pH)
    (generatedAxisGlobalTwelveRepresentative 7)) = wGoctadE9pL.real := by
  have hT := (tensorPlanF_actual wGoctadE9pHPlan wGoctadE9pHPlan_ok (eighthSrcXT_bnd (w := 64) (by
      norm_num))
    (by rw [wGoctadE9pHPlan_word, wGoctadE9pH_growth]; norm_num) (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1))).2
  rw [wGoctadE9pHPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 64) wGoctadE9pHW wGoctadE9pH_check wGoctadE9pHD
      wGoctadE9pD_ok.1 wGoctadE9pHD_cols
    wGoctadE9pHD_rows wGoctadE9pHT wGoctadE9pHT_check _ hT _ (eighthSrcT_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
