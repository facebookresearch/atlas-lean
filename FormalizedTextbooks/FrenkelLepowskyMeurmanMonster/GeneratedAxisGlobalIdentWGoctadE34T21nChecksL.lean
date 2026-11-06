/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[47]- <-> Tenth[26]+
(record goctad:E34@T21-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadE34T21nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadE34T21nH : List IdentLetter := wGoctadE34T21nHW.map Prod.fst

/-- The target word. -/
def wGoctadE34T21nG : List IdentLetter := wGoctadE34T21nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE34T21nH`. -/
def wGoctadE34T21nHPlan : List TPlan :=
  [.letter (.qel (qmElt (14427251, false))),
    .letter (.sign 1566 0),
    .run
      [(1, false), (0, true), (0, true), (1, false), (0, true), (0, true), (1, false),
        (0, false), (1, false), (0, true), (1, false), (0, false), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (0, true), (0, true), (1, true), (0, false), (0, false), (1, true), (0, false),
        (1, true), (0, false), (0, false), (1, true), (0, false), (0, false), (0, false),
        (1, true), (0, false), (0, false), (0, false), (1, true), (0, false), (1, true),
        (0, true), (0, true), (1, false), (0, true), (1, false), (0, false), (0, false),
        (1, false), (0, true), (1, false), (0, false), (0, false), (0, false),
        (1, false), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false),
        (1, false), (0, false), (0, false), (1, false), (0, true), (1, false), (0, true)]
      [.trans 4 5, .trans 6 7, .trans 4 6, .trans 10 11, .trans 7 10, .trans 3 9, .trans 4 9,
        .trans 9 3, .trans 10 2, .trans 9 2, .trans 7 4, .trans 4 11, .trans 0 10,
        .trans 10 4, .trans 5 6, .trans 2 7, .trans 0 1, .trans 4 8, .trans 8 9,
        .trans 9 6, .trans 6 3, .trans 6 1, .trans 4 1, .trans 1 7, .trans 7 0,
        .trans 5 0, .trans 7 6, .trans 7 11, .trans 0 3, .trans 3 8, .trans 7 10,
        .trans 2 9, .trans 9 8, .trans 8 3, .trans 8 1, .trans 3 10],
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
      [(0, true), (0, true), (1, true)]
      [.trans 5 4, .trans 7 1, .trans 8 3, .trans 3 5, .trans 9 10, .trans 6 7, .trans 1 9,
        .trans 9 0, .trans 10 8, .trans 8 6, .trans 6 2, .trans 7 4, .trans 5 11,
        .trans 7 11, .trans 9 11, .trans 0 4, .trans 4 9, .trans 9 3, .trans 9 2,
        .trans 9 1, .trans 2 7, .trans 9 11, .trans 5 7, .trans 1 7, .trans 7 2,
        .trans 7 10, .trans 0 3, .trans 3 8, .trans 3 10, .trans 8 3, .trans 8 6,
        .trans 6 8, .trans 6 5, .trans 5 0, .trans 0 4, .trans 4 2, .trans 2 6,
        .trans 2 8, .trans 8 10, .trans 10 1, .trans 1 6, .trans 6 5, .trans 1 3],
    .letter (.xi),
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadE34T21nHPlan_word : planWord wGoctadE34T21nHPlan = wGoctadE34T21nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE34T21nHPlan_ok : planOk wGoctadE34T21nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE34T21nG`. -/
def wGoctadE34T21nGPlan : List TPlan :=
  [.letter (.qel (qmElt (63269, false))),
    .letter (.sign 215 0),
    .run
      [(1, false), (0, false), (0, false), (0, false), (1, false), (0, false), (0, false),
        (1, false), (0, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false),
        (0, false), (0, false), (1, false), (0, true), (0, true), (1, true), (0, true),
        (1, true), (0, false), (1, true), (0, true), (0, true), (0, true), (1, true),
        (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (1, true),
        (0, false), (1, true), (0, true), (0, true), (0, true), (1, true), (0, true),
        (1, false), (0, false), (1, false), (0, true), (0, true), (0, true), (1, false),
        (0, false), (1, false), (0, false), (0, false), (0, false), (1, false),
        (0, true), (1, false), (0, false), (1, false), (0, true), (0, true)]
      [.trans 2 9, .trans 5 4, .trans 4 3, .trans 1 2, .trans 8 10, .trans 1 6, .trans 6 1,
        .trans 4 0, .trans 7 0, .trans 10 11, .trans 0 2, .trans 2 8, .trans 8 4,
        .trans 3 7, .trans 7 1, .trans 0 6, .trans 2 9, .trans 9 7, .trans 10 9,
        .trans 7 9, .trans 9 10, .trans 7 5, .trans 10 3, .trans 0 5, .trans 5 1,
        .trans 9 2, .trans 9 8, .trans 1 3, .trans 8 6, .trans 3 6, .trans 5 0,
        .trans 0 5, .trans 2 4, .trans 4 0, .trans 4 5, .trans 5 2, .trans 5 4],
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
theorem wGoctadE34T21nGPlan_word : planWord wGoctadE34T21nGPlan = wGoctadE34T21nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE34T21nGPlan_ok : planOk wGoctadE34T21nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadE34T21nHX : List SVec := tensorPlanF 72 wGoctadE34T21nHPlan (eighthSrcXT 72)

/-- The packed tensor of the target image. -/
def wGoctadE34T21nGX : List SVec := tensorPlanF 72 wGoctadE34T21nGPlan (tenthSrcXL 72)

/-- The representation of the source image. -/
def wGoctadE34T21nL : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGoctadE34T21nH, ShortData.ofList wGoctadE34T21nHT, (1 /
      32),
    tensorRat 72 wGoctadE34T21nHX ((tensorWordDenAll wGoctadE34T21nH : ℚ) * (2 *
        ((tensorWordDenAll srcEighthH : ℚ) * 1)))⟩

/-- The representation of the target image. -/
def wGoctadE34T21nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGoctadE34T21nG, ShortData.ofList wGoctadE34T21nGT, (1 /
      128),
    tensorRat 72 wGoctadE34T21nGX ((tensorWordDenAll wGoctadE34T21nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadE34T21nH_check : wGoctadE34T21nHW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadE34T21nD_ok : wGoctadE34T21nHD.ok = true ∧ wGoctadE34T21nGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadE34T21nHD_cols : ∀ i : Fin 24, qmWordP (wGoctadE34T21nHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGoctadE34T21nHD.colsP i.val, wGoctadE34T21nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadE34T21nHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE34T21nHD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE34T21nHD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadE34T21nHT_check : shortCheckF wGoctadE34T21nHD eighthShS.flat wGoctadE34T21nHT =
    true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadE34T21nT_labels : wGoctadE34T21nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGoctadE34T21nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadE34T21nH_growth : tensorWordGrowthAll wGoctadE34T21nH * (2 ^ 13 - 1) =
    18444492273895866368 := by decide

/-- The word bound of the target word. -/
theorem wGoctadE34T21nG_growth : tensorWordGrowthAll wGoctadE34T21nG * 15 = 515396075520 := by
    decide

/-- The coordinates of the source image. -/
theorem wGoctadE34T21nL_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE34T21nH)
    (generatedAxisGlobalTwelveRepresentative 7)) = wGoctadE34T21nL.real := by
  have hT := (tensorPlanF_actual wGoctadE34T21nHPlan wGoctadE34T21nHPlan_ok (eighthSrcXT_bnd (w :=
      72) (by norm_num))
    (by rw [wGoctadE34T21nHPlan_word, wGoctadE34T21nH_growth]; norm_num) (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1))).2
  rw [wGoctadE34T21nHPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 72) wGoctadE34T21nHW wGoctadE34T21nH_check
      wGoctadE34T21nHD wGoctadE34T21nD_ok.1 wGoctadE34T21nHD_cols
    wGoctadE34T21nHD_rows wGoctadE34T21nHT wGoctadE34T21nHT_check _ hT _ (eighthSrcT_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
