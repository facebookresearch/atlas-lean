/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGoctadE18nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[23]- <-> Tenth[58]-
(record goctad:E18-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadXGoctadE18nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadXGoctadE18nH : List IdentLetter := wGoctadXGoctadE18nHW.map Prod.fst

/-- The target word. -/
def wGoctadXGoctadE18nG : List IdentLetter := wGoctadXGoctadE18nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadXGoctadE18nH`. -/
def wGoctadXGoctadE18nHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(0, true), (1, false)]
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
    .run
      [(0, true), (0, true)]
      [.trans 1 2, .trans 8 3, .trans 10 5, .trans 8 9, .trans 2 8, .trans 4 7, .trans 7 0,
        .trans 4 8, .trans 8 3, .trans 5 9, .trans 5 4, .trans 10 6, .trans 6 4,
        .trans 6 8, .trans 5 10, .trans 10 1, .trans 0 4, .trans 3 2, .trans 2 11,
        .trans 7 6, .trans 6 7, .trans 6 9, .trans 0 2, .trans 9 11, .trans 4 6,
        .trans 7 10, .trans 10 11, .trans 9 2, .trans 6 1, .trans 1 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadXGoctadE18nHPlan_word : planWord wGoctadXGoctadE18nHPlan = wGoctadXGoctadE18nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadXGoctadE18nHPlan_ok : planOk wGoctadXGoctadE18nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadXGoctadE18nG`. -/
def wGoctadXGoctadE18nGPlan : List TPlan :=
  [.letter (.qel (qmElt (11224481, true))),
    .letter (.sign 1987 0),
    .run
      [(0, true), (1, false), (0, false), (0, false), (0, false), (1, false), (0, false),
        (1, false), (0, true), (1, false), (0, false), (1, false), (0, false),
        (1, false), (0, true), (1, false), (0, true), (0, true), (0, true), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, false), (1, true), (0, true),
        (0, true), (1, true), (0, true), (1, true), (0, false), (1, true), (0, true),
        (0, true), (1, true), (0, true), (1, true), (0, false), (0, false), (1, true),
        (0, true), (1, true), (0, true), (0, true), (0, true), (0, true), (1, false),
        (0, false), (0, false), (0, false), (1, false), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, false), (1, false), (0, true), (0, true),
        (1, false), (0, false), (1, false), (0, false), (0, false), (0, false),
        (1, false)]
      [.trans 8 1, .trans 6 4, .trans 5 10, .trans 1 2, .trans 2 11, .trans 2 3, .trans 0 2,
        .trans 10 5, .trans 5 8, .trans 4 9, .trans 10 9, .trans 1 8, .trans 7 10,
        .trans 5 7, .trans 7 5, .trans 9 1, .trans 8 9, .trans 9 8, .trans 5 6,
        .trans 10 0, .trans 0 3, .trans 0 6, .trans 3 2, .trans 3 9, .trans 4 6,
        .trans 6 7, .trans 7 0, .trans 7 2, .trans 7 3, .trans 7 4, .trans 7 9,
        .trans 7 11, .trans 9 1],
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
theorem wGoctadXGoctadE18nGPlan_word : planWord wGoctadXGoctadE18nGPlan = wGoctadXGoctadE18nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadXGoctadE18nGPlan_ok : planOk wGoctadXGoctadE18nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadXGoctadE18nHX : List SVec := tensorPlanF 64 wGoctadXGoctadE18nHPlan (eighthSrcXT 64)

/-- The packed tensor of the target image. -/
def wGoctadXGoctadE18nGX : List SVec := tensorPlanF 64 wGoctadXGoctadE18nGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGoctadXGoctadE18nL : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGoctadXGoctadE18nH, ShortData.ofList
      wGoctadXGoctadE18nHT, (1 / 32),
    tensorRat 64 wGoctadXGoctadE18nHX ((tensorWordDenAll wGoctadXGoctadE18nH : ℚ) * (2 *
        ((tensorWordDenAll srcEighthH : ℚ) * 1)))⟩

/-- The representation of the target image. -/
def wGoctadXGoctadE18nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGoctadXGoctadE18nG, ShortData.ofList
      wGoctadXGoctadE18nGT, (1 / 128),
    tensorRat 64 wGoctadXGoctadE18nGX ((tensorWordDenAll wGoctadXGoctadE18nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadXGoctadE18nH_check : wGoctadXGoctadE18nHW.all (fun p => identLetterCheckP p.1 p.2)
    = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadXGoctadE18nD_ok : wGoctadXGoctadE18nHD.ok = true ∧ wGoctadXGoctadE18nGD.ok = true
    := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadXGoctadE18nHD_cols : ∀ i : Fin 24, qmWordP (wGoctadXGoctadE18nHW.map Prod.snd) (2 ^
    i.val, false) =
    (fld 24 wGoctadXGoctadE18nHD.colsP i.val, wGoctadXGoctadE18nHD.coeff.testBit i.val) := by
        decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadXGoctadE18nHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadXGoctadE18nHD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadXGoctadE18nHD.colsP
        j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadXGoctadE18nHT_check : shortCheckF wGoctadXGoctadE18nHD eighthShS.flat
    wGoctadXGoctadE18nHT = true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadXGoctadE18nT_labels : wGoctadXGoctadE18nHT.all (fun p => decide (p.1 < 98280)) =
    true ∧
    wGoctadXGoctadE18nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadXGoctadE18nH_growth : tensorWordGrowthAll wGoctadXGoctadE18nH * (2 ^ 13 - 1) =
    536805376 := by decide

/-- The word bound of the target word. -/
theorem wGoctadXGoctadE18nG_growth : tensorWordGrowthAll wGoctadXGoctadE18nG * 15 = 515396075520
    := by decide

/-- The coordinates of the source image. -/
theorem wGoctadXGoctadE18nL_actual : griessConwayEncode (rhoLocal (identWordLocal
    wGoctadXGoctadE18nH)
    (generatedAxisGlobalTwelveRepresentative 7)) = wGoctadXGoctadE18nL.real := by
  have hT := (tensorPlanF_actual wGoctadXGoctadE18nHPlan wGoctadXGoctadE18nHPlan_ok
      (eighthSrcXT_bnd (w := 64) (by norm_num))
    (by rw [wGoctadXGoctadE18nHPlan_word, wGoctadXGoctadE18nH_growth]; norm_num) (2 *
        ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [wGoctadXGoctadE18nHPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 64) wGoctadXGoctadE18nHW wGoctadXGoctadE18nH_check
      wGoctadXGoctadE18nHD wGoctadXGoctadE18nD_ok.1 wGoctadXGoctadE18nHD_cols
    wGoctadXGoctadE18nHD_rows wGoctadXGoctadE18nHT wGoctadXGoctadE18nHT_check _ hT _
        (eighthSrcT_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
