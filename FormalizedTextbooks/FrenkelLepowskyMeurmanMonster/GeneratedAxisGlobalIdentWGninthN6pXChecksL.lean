/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN6pXData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Ninth[10]+ <-> Twelfth[12]-
(record gninth:N6+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGninthN6pXChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGninthN6pXH : List IdentLetter := wGninthN6pXHW.map Prod.fst

/-- The target word. -/
def wGninthN6pXG : List IdentLetter := wGninthN6pXGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN6pXH`. -/
def wGninthN6pXHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.xi),
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN6pXHPlan_word : planWord wGninthN6pXHPlan = wGninthN6pXH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN6pXHPlan_ok : planOk wGninthN6pXHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN6pXG`. -/
def wGninthN6pXGPlan : List TPlan :=
  [.letter (.qel (qmElt (269700, true))),
    .letter (.sign 62 0),
    .run
      [(0, true), (0, true), (1, false), (0, false), (1, false), (0, false), (0, false),
        (1, false), (0, false), (1, false), (0, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (1, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, false), (1, false)]
      [.trans 7 1, .trans 8 10, .trans 1 9, .trans 4 1, .trans 0 2, .trans 2 0, .trans 5 8,
        .trans 6 5, .trans 3 1, .trans 1 0, .trans 1 5, .trans 0 8, .trans 7 6,
        .trans 6 9, .trans 5 6, .trans 9 3, .trans 3 9, .trans 9 10, .trans 9 8,
        .trans 10 2, .trans 10 4, .trans 3 1, .trans 1 7, .trans 0 4, .trans 2 6,
        .trans 2 7, .trans 7 4, .trans 4 7, .trans 5 4, .trans 6 5, .trans 6 7,
        .trans 7 2, .trans 7 5, .trans 7 6, .trans 7 8, .trans 8 0, .trans 8 4,
        .trans 8 5, .trans 8 6],
    .letter (.xi),
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
theorem wGninthN6pXGPlan_word : planWord wGninthN6pXGPlan = wGninthN6pXG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN6pXGPlan_ok : planOk wGninthN6pXGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGninthN6pXHX : List SVec := tensorPlanF 64 wGninthN6pXHPlan (ninthSrcXL 64)

/-- The packed tensor of the target image. -/
def wGninthN6pXGX : List SVec := tensorPlanF 64 wGninthN6pXGPlan (twelfthSrcXW 64)

/-- The representation of the source image. -/
def wGninthN6pXL : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN6pXH, ShortData.ofList wGninthN6pXHT, (1 / 128),
    tensorRat 64 wGninthN6pXHX ((tensorWordDenAll wGninthN6pXH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGninthN6pXW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet wGninthN6pXG, ShortData.ofList wGninthN6pXGT, (1 / 128),
    tensorRat 64 wGninthN6pXGX ((tensorWordDenAll wGninthN6pXG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGninthN6pXH_check : wGninthN6pXHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGninthN6pXD_ok : wGninthN6pXHD.ok = true ∧ wGninthN6pXGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGninthN6pXHD_cols : ∀ i : Fin 24, qmWordP (wGninthN6pXHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN6pXHD.colsP i.val, wGninthN6pXHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGninthN6pXHD_rows : ∀ i : Fin 24,
    fld 24 wGninthN6pXHD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN6pXHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem wGninthN6pXHT_check0 :
    shortCheckPk wGninthN6pXHD 10 15 ((srcNinthCShort.flat).take 15360) ((wGninthN6pXHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem wGninthN6pXHT_check1 :
    shortCheckPk wGninthN6pXHD 10 15 (((srcNinthCShort.flat).drop 15360).take 15360)
        (((wGninthN6pXHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem wGninthN6pXHT_check2 :
    shortCheckPk wGninthN6pXHD 10 15 ((((srcNinthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN6pXHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem wGninthN6pXHT_check3 :
    shortCheckPk wGninthN6pXHD 10 15 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).take 15360) (((((wGninthN6pXHT).drop 15360).drop 15360).drop 15360).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 4). -/
theorem wGninthN6pXHT_check4 :
    shortCheckPk wGninthN6pXHD 10 1 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).drop 15360) (((((wGninthN6pXHT).drop 15360).drop 15360).drop 15360).drop 15360) =
        true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem wGninthN6pXHT_check : shortCheckF wGninthN6pXHD srcNinthCShort.flat wGninthN6pXHT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN6pXHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN6pXHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN6pXHT_check2)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN6pXHT_check3)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN6pXHT_check4))))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGninthN6pXT_labels : wGninthN6pXHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGninthN6pXGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGninthN6pXH_growth : tensorWordGrowthAll wGninthN6pXH * 15 = 64424509440 := by decide

/-- The word bound of the target word. -/
theorem wGninthN6pXG_growth : tensorWordGrowthAll wGninthN6pXG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem wGninthN6pXL_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN6pXH)
    (generatedAxisGlobalTwelveRepresentative 8)) = wGninthN6pXL.real := by
  have hT := (tensorPlanF_actual wGninthN6pXHPlan wGninthN6pXHPlan_ok (ninthSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN6pXHPlan_word, wGninthN6pXH_growth]; norm_num) 32).2
  rw [wGninthN6pXHPlan_word] at hT
  exact IdentVec.word_actual (ninthSrcVecL 64) wGninthN6pXHW wGninthN6pXH_check wGninthN6pXHD
      wGninthN6pXD_ok.1 wGninthN6pXHD_cols
    wGninthN6pXHD_rows wGninthN6pXHT wGninthN6pXHT_check _ hT _ (ninthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
