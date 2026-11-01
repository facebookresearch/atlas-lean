/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[8]- <-> Tenth[40]+
(record goctad:E4@T26-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadE4T26nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadE4T26nH : List IdentLetter := wGoctadE4T26nHW.map Prod.fst

/-- The target word. -/
def wGoctadE4T26nG : List IdentLetter := wGoctadE4T26nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE4T26nH`. -/
def wGoctadE4T26nHPlan : List TPlan :=
  [.letter (.qel (qmElt (9152780, false))),
    .letter (.sign 1286 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, true), (1, false), (0, true), (0, true), (0, true),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, true), (0, true),
        (0, true), (1, true), (0, false), (0, false), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, true),
        (0, true), (1, true), (0, false), (1, true), (0, false), (0, false), (1, true),
        (0, true), (0, true), (0, true), (1, false), (0, false), (1, false), (0, false),
        (0, false), (0, false), (1, false), (0, false), (0, false), (1, false),
        (0, false), (0, false), (1, false), (0, false), (0, false), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (1, false)]
      [.trans 4 8, .trans 5 4, .trans 3 11, .trans 7 5, .trans 7 2, .trans 2 3, .trans 10 0,
        .trans 0 7, .trans 4 1, .trans 1 2, .trans 4 10, .trans 6 10, .trans 7 11,
        .trans 10 0, .trans 7 6, .trans 10 9, .trans 9 3, .trans 7 8, .trans 9 5,
        .trans 4 5, .trans 5 7, .trans 6 7, .trans 7 5, .trans 7 3, .trans 3 2,
        .trans 2 8, .trans 8 4, .trans 0 11, .trans 1 0, .trans 1 11, .trans 4 5,
        .trans 5 6, .trans 6 0, .trans 6 1, .trans 6 4, .trans 6 5, .trans 6 11],
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
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadE4T26nHPlan_word : planWord wGoctadE4T26nHPlan = wGoctadE4T26nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE4T26nHPlan_ok : planOk wGoctadE4T26nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE4T26nG`. -/
def wGoctadE4T26nGPlan : List TPlan :=
  [.letter (.qel (qmElt (672503, false))),
    .letter (.sign 682 0),
    .run
      [(1, false), (0, true), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, true), (0, true), (1, true),
        (0, false), (1, true), (0, true), (0, true), (0, true), (1, true), (0, false),
        (1, true), (0, true), (0, true), (1, true), (0, true), (0, true), (1, true),
        (0, true), (1, true), (0, true), (0, true), (1, true), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, false), (1, false), (0, true), (0, true),
        (1, false), (0, true), (1, false), (0, true), (0, true), (1, false), (0, true),
        (0, true), (1, false), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, true)]
      [.trans 4 7, .trans 3 5, .trans 2 4, .trans 2 0, .trans 7 5, .trans 4 11, .trans 1 2,
        .trans 8 9, .trans 2 3, .trans 5 7, .trans 3 4, .trans 4 10, .trans 10 1,
        .trans 2 1, .trans 1 3, .trans 9 4, .trans 7 9, .trans 9 7, .trans 7 1,
        .trans 3 0, .trans 0 10, .trans 10 8, .trans 4 6, .trans 0 2, .trans 8 6,
        .trans 3 6, .trans 8 5, .trans 1 10, .trans 2 6, .trans 6 8, .trans 8 9,
        .trans 2 11, .trans 8 6],
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
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadE4T26nGPlan_word : planWord wGoctadE4T26nGPlan = wGoctadE4T26nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE4T26nGPlan_ok : planOk wGoctadE4T26nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadE4T26nHX : List SVec := tensorPlanF 64 wGoctadE4T26nHPlan (eighthSrcXT 64)

/-- The packed tensor of the target image. -/
def wGoctadE4T26nGX : List SVec := tensorPlanF 64 wGoctadE4T26nGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGoctadE4T26nL : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGoctadE4T26nH, ShortData.ofList wGoctadE4T26nHT, (1 / 32),
    tensorRat 64 wGoctadE4T26nHX ((tensorWordDenAll wGoctadE4T26nH : ℚ) * (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1)))⟩

/-- The representation of the target image. -/
def wGoctadE4T26nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGoctadE4T26nG, ShortData.ofList wGoctadE4T26nGT, (1 / 128),
    tensorRat 64 wGoctadE4T26nGX ((tensorWordDenAll wGoctadE4T26nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadE4T26nH_check : wGoctadE4T26nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadE4T26nD_ok : wGoctadE4T26nHD.ok = true ∧ wGoctadE4T26nGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadE4T26nHD_cols : ∀ i : Fin 24, qmWordP (wGoctadE4T26nHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGoctadE4T26nHD.colsP i.val, wGoctadE4T26nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadE4T26nHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE4T26nHD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE4T26nHD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadE4T26nHT_check : shortCheckF wGoctadE4T26nHD eighthShS.flat wGoctadE4T26nHT = true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadE4T26nT_labels : wGoctadE4T26nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGoctadE4T26nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadE4T26nH_growth : tensorWordGrowthAll wGoctadE4T26nH * (2 ^ 13 - 1) =
    72048797944905728 := by decide

/-- The word bound of the target word. -/
theorem wGoctadE4T26nG_growth : tensorWordGrowthAll wGoctadE4T26nG * 15 = 33776997205278720 := by
    decide

/-- The coordinates of the source image. -/
theorem wGoctadE4T26nL_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE4T26nH)
    (generatedAxisGlobalTwelveRepresentative 7)) = wGoctadE4T26nL.real := by
  have hT := (tensorPlanF_actual wGoctadE4T26nHPlan wGoctadE4T26nHPlan_ok (eighthSrcXT_bnd (w :=
      64) (by norm_num))
    (by rw [wGoctadE4T26nHPlan_word, wGoctadE4T26nH_growth]; norm_num) (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1))).2
  rw [wGoctadE4T26nHPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 64) wGoctadE4T26nHW wGoctadE4T26nH_check
      wGoctadE4T26nHD wGoctadE4T26nD_ok.1 wGoctadE4T26nHD_cols
    wGoctadE4T26nHD_rows wGoctadE4T26nHT wGoctadE4T26nHT_check _ hT _ (eighthSrcT_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
