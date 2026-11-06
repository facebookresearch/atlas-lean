/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[13]- <-> Eighth[13]-
(record goctad:E9-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadE9nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadE9nH : List IdentLetter := wGoctadE9nHW.map Prod.fst

/-- The target word. -/
def wGoctadE9nG : List IdentLetter := wGoctadE9nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE9nH`. -/
def wGoctadE9nHPlan : List TPlan :=
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
theorem wGoctadE9nHPlan_word : planWord wGoctadE9nHPlan = wGoctadE9nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE9nHPlan_ok : planOk wGoctadE9nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE9nG`. -/
def wGoctadE9nGPlan : List TPlan :=
  [.letter (.qel (qmElt (11196416, true))),
    .letter (.sign 262 0),
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
theorem wGoctadE9nGPlan_word : planWord wGoctadE9nGPlan = wGoctadE9nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE9nGPlan_ok : planOk wGoctadE9nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadE9nHX : List SVec := tensorPlanF 64 wGoctadE9nHPlan (eighthSrcXT 64)

/-- The packed tensor of the target image. -/
def wGoctadE9nGX : List SVec := tensorPlanF 64 wGoctadE9nGPlan (eighthSrcXT 64)

/-- The representation of the source image. -/
def wGoctadE9nL : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGoctadE9nH, ShortData.ofList wGoctadE9nHT, (1 / 32),
    tensorRat 64 wGoctadE9nHX ((tensorWordDenAll wGoctadE9nH : ℚ) * (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1)))⟩

/-- The representation of the target image. -/
def wGoctadE9nW : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGoctadE9nG, ShortData.ofList wGoctadE9nGT, (1 / 32),
    tensorRat 64 wGoctadE9nGX ((tensorWordDenAll wGoctadE9nG : ℚ) * (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1)))⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadE9nH_check : wGoctadE9nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadE9nD_ok : wGoctadE9nHD.ok = true ∧ wGoctadE9nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadE9nHD_cols : ∀ i : Fin 24, qmWordP (wGoctadE9nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGoctadE9nHD.colsP i.val, wGoctadE9nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadE9nHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE9nHD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE9nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadE9nHT_check : shortCheckF wGoctadE9nHD eighthShS.flat wGoctadE9nHT = true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadE9nT_labels : wGoctadE9nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGoctadE9nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadE9nH_growth : tensorWordGrowthAll wGoctadE9nH * (2 ^ 13 - 1) = 536805376 := by decide

/-- The word bound of the target word. -/
theorem wGoctadE9nG_growth : tensorWordGrowthAll wGoctadE9nG * (2 ^ 13 - 1) = 4294443008 := by
    decide

/-- The coordinates of the source image. -/
theorem wGoctadE9nL_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE9nH)
    (generatedAxisGlobalTwelveRepresentative 7)) = wGoctadE9nL.real := by
  have hT := (tensorPlanF_actual wGoctadE9nHPlan wGoctadE9nHPlan_ok (eighthSrcXT_bnd (w := 64) (by
      norm_num))
    (by rw [wGoctadE9nHPlan_word, wGoctadE9nH_growth]; norm_num) (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1))).2
  rw [wGoctadE9nHPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 64) wGoctadE9nHW wGoctadE9nH_check wGoctadE9nHD
      wGoctadE9nD_ok.1 wGoctadE9nHD_cols
    wGoctadE9nHD_rows wGoctadE9nHT wGoctadE9nHT_check _ hT _ (eighthSrcT_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
