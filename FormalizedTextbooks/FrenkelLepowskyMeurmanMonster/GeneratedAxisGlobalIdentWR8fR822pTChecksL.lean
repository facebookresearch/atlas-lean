/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822pTData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[4]+ <-> Sixth[14]+
(record r8f:R822+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR822pTChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR822pTH : List IdentLetter := wR8fR822pTHW.map Prod.fst

/-- The target word. -/
def wR8fR822pTG : List IdentLetter := wR8fR822pTGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR822pTH`. -/
def wR8fR822pTHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(0, false), (1, true), (0, true), (1, true)]
      [.trans 0 4, .trans 6 2, .trans 0 7, .trans 0 3, .trans 3 6, .trans 9 10, .trans 5 1,
        .trans 9 7, .trans 3 11, .trans 7 5, .trans 10 0, .trans 7 11, .trans 2 3,
        .trans 8 9, .trans 2 0, .trans 3 5, .trans 8 4, .trans 1 5, .trans 5 3,
        .trans 1 0, .trans 6 0, .trans 5 2, .trans 2 8, .trans 8 7, .trans 0 1,
        .trans 0 3, .trans 8 2, .trans 0 5, .trans 8 5, .trans 7 10, .trans 10 9,
        .trans 9 1, .trans 1 11, .trans 4 6, .trans 6 9, .trans 9 4, .trans 9 6],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR822pTHPlan_word : planWord wR8fR822pTHPlan = wR8fR822pTH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR822pTHPlan_ok : planOk wR8fR822pTHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR822pTG`. -/
def wR8fR822pTGPlan : List TPlan :=
  [.letter (.qel (qmElt (15804414, false))),
    .letter (.sign 1385 0),
    .run
      [(1, false), (0, true), (1, false), (0, true), (0, true), (0, true), (1, false),
        (0, true), (1, false), (0, false), (0, false), (0, false), (1, false),
        (0, false), (0, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, false), (1, false), (0, false), (0, false), (1, true), (0, false), (1, true),
        (0, true), (0, true), (1, true), (0, false), (1, true), (0, true), (1, true),
        (0, true), (1, true), (0, false), (0, false), (0, false), (1, true), (0, true),
        (0, true), (1, true), (0, false), (0, false), (1, false), (0, false), (1, false),
        (0, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, true),
        (1, false), (0, true)]
      [.trans 8 0, .trans 10 8, .trans 1 10, .trans 2 9, .trans 3 2, .trans 1 3, .trans 4 5,
        .trans 9 1, .trans 3 4, .trans 0 1, .trans 2 5, .trans 1 2, .trans 7 4,
        .trans 7 6, .trans 6 5, .trans 1 3, .trans 3 10, .trans 2 9, .trans 10 8,
        .trans 8 0],
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
      [(0, true), (0, true), (0, true)]
      [.trans 2 3, .trans 8 2, .trans 10 2, .trans 10 0, .trans 7 10, .trans 3 8, .trans 0 7,
        .trans 7 6, .trans 5 0, .trans 7 9, .trans 6 2, .trans 5 6, .trans 6 5,
        .trans 5 6, .trans 0 1, .trans 5 10, .trans 10 11, .trans 10 4, .trans 4 8,
        .trans 6 3, .trans 7 4, .trans 6 4, .trans 4 7, .trans 2 9, .trans 7 4,
        .trans 1 9, .trans 9 8, .trans 8 11, .trans 2 3, .trans 8 3]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR822pTGPlan_word : planWord wR8fR822pTGPlan = wR8fR822pTG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR822pTGPlan_ok : planOk wR8fR822pTGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR822pTHX : List SVec := tensorPlanF 64 wR8fR822pTHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR822pTGX : List SVec := tensorPlanF 64 wR8fR822pTGPlan (sixthSXF 64)

/-- The representation of the source image. -/
def wR8fR822pTL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR822pTH, ShortData.ofList wR8fR822pTHT, (1 / 128),
    tensorRat 64 wR8fR822pTHX ((tensorWordDenAll wR8fR822pTH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR822pTW : IdentVec :=
  ⟨sixthSrcMat.act identSpatialAlphabet wR8fR822pTG, ShortData.ofList wR8fR822pTGT, 1 / 32,
    tensorRat 64 wR8fR822pTGX ((tensorWordDenAll wR8fR822pTG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR822pTH_check : wR8fR822pTHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR822pTD_ok : wR8fR822pTHD.ok = true ∧ wR8fR822pTGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR822pTHD_cols : ∀ i : Fin 24, qmWordP (wR8fR822pTHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR822pTHD.colsP i.val, wR8fR822pTHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR822pTHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR822pTHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR822pTHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR822pTHT_check : shortCheckF wR8fR822pTHD srcRootEightCShort.flat wR8fR822pTHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR822pTT_labels : wR8fR822pTHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR822pTGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR822pTH_growth : tensorWordGrowthAll wR8fR822pTH * 15 = 983040 := by decide

/-- The word bound of the target word. -/
theorem wR8fR822pTG_growth : tensorWordGrowthAll wR8fR822pTG * (2 ^ 8 - 1) = 8761733283840 := by
    decide

/-- The coordinates of the source image. -/
theorem wR8fR822pTL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR822pTH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR822pTL.real := by
  have hT := (tensorPlanF_actual wR8fR822pTHPlan wR8fR822pTHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR822pTHPlan_word, wR8fR822pTH_growth]; norm_num) 32).2
  rw [wR8fR822pTHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR822pTHW wR8fR822pTH_check wR8fR822pTHD
      wR8fR822pTD_ok.1 wR8fR822pTHD_cols
    wR8fR822pTHD_rows wR8fR822pTHT wR8fR822pTHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
