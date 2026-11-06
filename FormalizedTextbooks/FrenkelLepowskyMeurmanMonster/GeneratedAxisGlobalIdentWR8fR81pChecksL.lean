/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[16]+ <-> Twelfth[24]+
(record r8f:R81+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR81pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR81pH : List IdentLetter := wR8fR81pHW.map Prod.fst

/-- The target word. -/
def wR8fR81pG : List IdentLetter := wR8fR81pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR81pH`. -/
def wR8fR81pHPlan : List TPlan :=
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
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR81pHPlan_word : planWord wR8fR81pHPlan = wR8fR81pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR81pHPlan_ok : planOk wR8fR81pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR81pG`. -/
def wR8fR81pGPlan : List TPlan :=
  [.letter (.qel (qmElt (14550255, false))),
    .letter (.sign 707 0),
    .run
      [(1, false), (0, false), (1, false), (0, false), (0, false), (0, false), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, false), (1, false), (0, true), (1, false), (0, true), (0, true), (0, true),
        (1, false), (0, false), (0, false), (1, false), (0, false), (0, false),
        (1, false), (0, false)]
      [.trans 7 3, .trans 0 2, .trans 1 0, .trans 9 1, .trans 4 10, .trans 9 7, .trans 0 4,
        .trans 9 11, .trans 7 2, .trans 2 8, .trans 0 6, .trans 1 3, .trans 2 9,
        .trans 10 5, .trans 3 9, .trans 9 7, .trans 7 5, .trans 5 10, .trans 5 0,
        .trans 8 4, .trans 8 11, .trans 10 1, .trans 1 8, .trans 8 1, .trans 3 6,
        .trans 6 11, .trans 6 3, .trans 6 5, .trans 6 2, .trans 0 6, .trans 4 0,
        .trans 4 6, .trans 4 8, .trans 6 0, .trans 6 4, .trans 6 7, .trans 6 8,
        .trans 6 11, .trans 8 3, .trans 8 9, .trans 9 2, .trans 9 6, .trans 9 7,
        .trans 9 11],
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
        .trans 8 4, .trans 8 5, .trans 8 6, .trans 8 7, .trans 8 9],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.sign 32 0),
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
theorem wR8fR81pGPlan_word : planWord wR8fR81pGPlan = wR8fR81pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR81pGPlan_ok : planOk wR8fR81pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR81pHX : List SVec := tensorPlanF 112 wR8fR81pHPlan (rootEightSrcXL 112)

/-- The packed tensor of the target image. -/
def wR8fR81pGX : List SVec := tensorPlanF 112 wR8fR81pGPlan (twelfthSrcXW 112)

/-- The representation of the source image. -/
def wR8fR81pL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR81pH, ShortData.ofList wR8fR81pHT, (1 / 128),
    tensorRat 112 wR8fR81pHX ((tensorWordDenAll wR8fR81pH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR81pW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet wR8fR81pG, ShortData.ofList wR8fR81pGT, (1 / 128),
    tensorRat 112 wR8fR81pGX ((tensorWordDenAll wR8fR81pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR81pH_check : wR8fR81pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR81pD_ok : wR8fR81pHD.ok = true ∧ wR8fR81pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR81pHD_cols : ∀ i : Fin 24, qmWordP (wR8fR81pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR81pHD.colsP i.val, wR8fR81pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR81pHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR81pHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR81pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR81pHT_check : shortCheckF wR8fR81pHD srcRootEightCShort.flat wR8fR81pHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR81pT_labels : wR8fR81pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR81pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR81pH_growth : tensorWordGrowthAll wR8fR81pH * 15 = 251658240 := by decide

/-- The word bound of the target word. -/
theorem wR8fR81pG_growth : tensorWordGrowthAll wR8fR81pG * 15 = 4123168604160 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR81pL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR81pH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR81pL.real := by
  have hT := (tensorPlanF_actual wR8fR81pHPlan wR8fR81pHPlan_ok (rootEightSrcXL_bnd (w := 112) (by
      norm_num))
    (by rw [wR8fR81pHPlan_word, wR8fR81pH_growth]; norm_num) 32).2
  rw [wR8fR81pHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 112) wR8fR81pHW wR8fR81pH_check wR8fR81pHD
      wR8fR81pD_ok.1 wR8fR81pHD_cols
    wR8fR81pHD_rows wR8fR81pHT wR8fR81pHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
