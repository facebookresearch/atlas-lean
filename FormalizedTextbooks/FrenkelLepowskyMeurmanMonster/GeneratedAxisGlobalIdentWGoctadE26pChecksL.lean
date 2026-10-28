/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[37]+ <-> Seventh[32]+
(record goctad:E26+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadE26pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadE26pH : List IdentLetter := wGoctadE26pHW.map Prod.fst

/-- The target word. -/
def wGoctadE26pG : List IdentLetter := wGoctadE26pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE26pH`. -/
def wGoctadE26pHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(1, false)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadE26pHPlan_word : planWord wGoctadE26pHPlan = wGoctadE26pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE26pHPlan_ok : planOk wGoctadE26pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE26pG`. -/
def wGoctadE26pGPlan : List TPlan :=
  [.letter (.qel (qmElt (14272520, true))),
    .letter (.sign 288 0),
    .run
      [(0, false), (1, false), (0, false), (1, false), (0, false), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, true), (0, true), (0, true), (1, false), (0, true),
        (0, true), (0, true), (1, false), (0, true), (0, true), (1, true), (0, true),
        (0, true), (1, true), (0, false), (0, false), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, true), (0, true), (0, true), (1, true), (0, false),
        (1, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, true),
        (1, false), (0, true), (1, false), (0, false), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, false), (1, false), (0, false), (0, false)]
      [.trans 2 1, .trans 7 8, .trans 9 1, .trans 4 0, .trans 0 11, .trans 4 9, .trans 1 2,
        .trans 4 5, .trans 5 2, .trans 10 0, .trans 6 7, .trans 7 9, .trans 9 3,
        .trans 7 1, .trans 1 11, .trans 10 5, .trans 0 3, .trans 5 8, .trans 8 9,
        .trans 9 2, .trans 3 2, .trans 2 3, .trans 3 1, .trans 1 2],
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
theorem wGoctadE26pGPlan_word : planWord wGoctadE26pGPlan = wGoctadE26pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE26pGPlan_ok : planOk wGoctadE26pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadE26pHX : List SVec := tensorPlanF 64 wGoctadE26pHPlan (eighthSrcXT 64)

/-- The packed tensor of the target image. -/
def wGoctadE26pGX : List SVec := tensorPlanF 64 wGoctadE26pGPlan (srcSeventhX0F 64)

/-- The representation of the source image. -/
def wGoctadE26pL : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGoctadE26pH, ShortData.ofList wGoctadE26pHT, (1 / 32),
    tensorRat 64 wGoctadE26pHX ((tensorWordDenAll wGoctadE26pH : ℚ) * (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1)))⟩

/-- The representation of the target image. -/
def wGoctadE26pW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet wGoctadE26pG, ShortData.ofList wGoctadE26pGT, (1 / 32),
    tensorRat 64 wGoctadE26pGX ((tensorWordDenAll wGoctadE26pG : ℚ) * srcSeventhD0)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadE26pH_check : wGoctadE26pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadE26pD_ok : wGoctadE26pHD.ok = true ∧ wGoctadE26pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadE26pHD_cols : ∀ i : Fin 24, qmWordP (wGoctadE26pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGoctadE26pHD.colsP i.val, wGoctadE26pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadE26pHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE26pHD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE26pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadE26pHT_check : shortCheckF wGoctadE26pHD eighthShS.flat wGoctadE26pHT = true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadE26pT_labels : wGoctadE26pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGoctadE26pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadE26pH_growth : tensorWordGrowthAll wGoctadE26pH * (2 ^ 13 - 1) = 2096896 := by decide

/-- The word bound of the target word. -/
theorem wGoctadE26pG_growth : tensorWordGrowthAll wGoctadE26pG * (4 * (16777216 * 8) + 276 * 6144)
    = 282364034940928 := by decide

/-- The coordinates of the source image. -/
theorem wGoctadE26pL_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE26pH)
    (generatedAxisGlobalTwelveRepresentative 7)) = wGoctadE26pL.real := by
  have hT := (tensorPlanF_actual wGoctadE26pHPlan wGoctadE26pHPlan_ok (eighthSrcXT_bnd (w := 64)
      (by norm_num))
    (by rw [wGoctadE26pHPlan_word, wGoctadE26pH_growth]; norm_num) (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1))).2
  rw [wGoctadE26pHPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 64) wGoctadE26pHW wGoctadE26pH_check wGoctadE26pHD
      wGoctadE26pD_ok.1 wGoctadE26pHD_cols
    wGoctadE26pHD_rows wGoctadE26pHT wGoctadE26pHT_check _ hT _ (eighthSrcT_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
