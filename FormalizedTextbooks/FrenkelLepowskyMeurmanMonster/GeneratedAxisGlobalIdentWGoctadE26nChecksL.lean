/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Eighth[37]- <-> Seventh[1]+
(record goctad:E26-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadE26nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadE26nH : List IdentLetter := wGoctadE26nHW.map Prod.fst

/-- The target word. -/
def wGoctadE26nG : List IdentLetter := wGoctadE26nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE26nH`. -/
def wGoctadE26nHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(1, false)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadE26nHPlan_word : planWord wGoctadE26nHPlan = wGoctadE26nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE26nHPlan_ok : planOk wGoctadE26nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadE26nG`. -/
def wGoctadE26nGPlan : List TPlan :=
  [.letter (.qel (qmElt (4076276, false))),
    .letter (.sign 714 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, true), (1, false), (0, true), (0, true), (0, true),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, true), (0, true),
        (0, true), (1, true), (0, false), (0, false), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, true),
        (0, true), (1, true), (0, false), (1, true), (0, false), (0, false), (1, true),
        (0, true), (1, false), (0, true), (0, true), (0, true), (1, false), (0, false),
        (1, false), (0, true), (1, false), (0, true), (0, true), (0, true), (1, false),
        (0, true), (1, false), (0, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, false), (0, false), (0, false)]
      [.trans 1 2, .trans 2 0, .trans 3 11, .trans 7 1, .trans 0 1, .trans 0 11, .trans 9 8,
        .trans 6 7, .trans 7 9, .trans 9 2, .trans 9 7, .trans 9 4, .trans 6 8,
        .trans 8 5, .trans 8 6, .trans 7 9, .trans 4 0, .trans 10 5, .trans 6 1,
        .trans 1 3, .trans 10 11, .trans 6 8, .trans 5 4, .trans 4 5, .trans 5 4,
        .trans 5 3, .trans 3 2, .trans 2 1],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadE26nGPlan_word : planWord wGoctadE26nGPlan = wGoctadE26nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadE26nGPlan_ok : planOk wGoctadE26nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadE26nHX : List SVec := tensorPlanF 64 wGoctadE26nHPlan (eighthSrcXT 64)

/-- The packed tensor of the target image. -/
def wGoctadE26nGX : List SVec := tensorPlanF 64 wGoctadE26nGPlan (srcSeventhX0F 64)

/-- The representation of the source image. -/
def wGoctadE26nL : IdentVec :=
  ⟨srcEighthMat.act identSpatialAlphabet wGoctadE26nH, ShortData.ofList wGoctadE26nHT, (1 / 32),
    tensorRat 64 wGoctadE26nHX ((tensorWordDenAll wGoctadE26nH : ℚ) * (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1)))⟩

/-- The representation of the target image. -/
def wGoctadE26nW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet wGoctadE26nG, ShortData.ofList wGoctadE26nGT, (1 / 32),
    tensorRat 64 wGoctadE26nGX ((tensorWordDenAll wGoctadE26nG : ℚ) * srcSeventhD0)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadE26nH_check : wGoctadE26nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadE26nD_ok : wGoctadE26nHD.ok = true ∧ wGoctadE26nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadE26nHD_cols : ∀ i : Fin 24, qmWordP (wGoctadE26nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGoctadE26nHD.colsP i.val, wGoctadE26nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadE26nHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE26nHD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE26nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadE26nHT_check : shortCheckF wGoctadE26nHD eighthShS.flat wGoctadE26nHT = true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadE26nT_labels : wGoctadE26nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGoctadE26nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadE26nH_growth : tensorWordGrowthAll wGoctadE26nH * (2 ^ 13 - 1) = 2096896 := by decide

/-- The word bound of the target word. -/
theorem wGoctadE26nG_growth : tensorWordGrowthAll wGoctadE26nG * (4 * (16777216 * 8) + 276 * 6144)
    = 282364034940928 := by decide

/-- The coordinates of the source image. -/
theorem wGoctadE26nL_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE26nH)
    (generatedAxisGlobalTwelveRepresentative 7)) = wGoctadE26nL.real := by
  have hT := (tensorPlanF_actual wGoctadE26nHPlan wGoctadE26nHPlan_ok (eighthSrcXT_bnd (w := 64)
      (by norm_num))
    (by rw [wGoctadE26nHPlan_word, wGoctadE26nH_growth]; norm_num) (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1))).2
  rw [wGoctadE26nHPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 64) wGoctadE26nHW wGoctadE26nH_check wGoctadE26nHD
      wGoctadE26nD_ok.1 wGoctadE26nHD_cols
    wGoctadE26nHD_rows wGoctadE26nHT wGoctadE26nHT_check _ hT _ (eighthSrcT_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
