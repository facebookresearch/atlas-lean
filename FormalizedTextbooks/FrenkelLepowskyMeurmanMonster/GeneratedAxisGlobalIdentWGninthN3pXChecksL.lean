/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pXData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Ninth[5]+ <-> Twelfth[31]+
(record gninth:N3+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGninthN3pXChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGninthN3pXH : List IdentLetter := wGninthN3pXHW.map Prod.fst

/-- The target word. -/
def wGninthN3pXG : List IdentLetter := wGninthN3pXGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN3pXH`. -/
def wGninthN3pXHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN3pXHPlan_word : planWord wGninthN3pXHPlan = wGninthN3pXH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN3pXHPlan_ok : planOk wGninthN3pXHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN3pXG`. -/
def wGninthN3pXGPlan : List TPlan :=
  [.letter (.qel (qmElt (10438696, true))),
    .letter (.sign 399 0),
    .run
      [(1, false), (0, true), (1, false), (0, false), (1, false), (0, true), (0, true),
        (1, false), (0, false), (0, false), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, true), (0, true), (0, true), (1, false), (0, true),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, false),
        (1, false)]
      [.trans 0 1, .trans 0 3, .trans 0 6, .trans 0 9, .trans 0 11, .trans 6 1, .trans 1 0,
        .trans 1 6, .trans 1 9, .trans 4 2, .trans 2 0, .trans 2 4, .trans 2 9,
        .trans 6 3, .trans 3 0, .trans 3 2, .trans 3 6, .trans 3 9, .trans 3 11,
        .trans 5 4, .trans 4 0, .trans 4 1, .trans 4 2, .trans 4 5, .trans 4 6,
        .trans 4 7, .trans 4 8, .trans 4 9, .trans 4 10, .trans 4 11, .trans 6 5,
        .trans 5 0, .trans 5 6, .trans 5 7, .trans 5 8, .trans 5 10, .trans 5 11,
        .trans 7 6, .trans 6 3, .trans 6 7, .trans 6 9, .trans 6 10, .trans 6 11,
        .trans 8 7, .trans 7 0, .trans 7 1, .trans 7 4, .trans 7 8, .trans 8 0,
        .trans 8 1, .trans 8 2, .trans 8 4, .trans 8 7, .trans 8 11, .trans 10 9,
        .trans 9 3, .trans 9 4, .trans 9 5, .trans 9 6, .trans 9 10, .trans 9 11,
        .trans 10 1, .trans 10 3, .trans 10 4, .trans 10 5, .trans 10 8, .trans 10 9,
        .trans 10 11],
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
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN3pXGPlan_word : planWord wGninthN3pXGPlan = wGninthN3pXG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN3pXGPlan_ok : planOk wGninthN3pXGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGninthN3pXHX : List SVec := tensorPlanF 64 wGninthN3pXHPlan (ninthSrcXL 64)

/-- The packed tensor of the target image. -/
def wGninthN3pXGX : List SVec := tensorPlanF 64 wGninthN3pXGPlan (twelfthSrcXW 64)

/-- The representation of the source image. -/
def wGninthN3pXL : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN3pXH, ShortData.ofList wGninthN3pXHT, (1 / 128),
    tensorRat 64 wGninthN3pXHX ((tensorWordDenAll wGninthN3pXH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGninthN3pXW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet wGninthN3pXG, ShortData.ofList wGninthN3pXGT, (1 / 128),
    tensorRat 64 wGninthN3pXGX ((tensorWordDenAll wGninthN3pXG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGninthN3pXH_check : wGninthN3pXHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGninthN3pXD_ok : wGninthN3pXHD.ok = true ∧ wGninthN3pXGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGninthN3pXHD_cols : ∀ i : Fin 24, qmWordP (wGninthN3pXHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN3pXHD.colsP i.val, wGninthN3pXHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGninthN3pXHD_rows : ∀ i : Fin 24,
    fld 24 wGninthN3pXHD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN3pXHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem wGninthN3pXHT_check0 :
    shortCheckPk wGninthN3pXHD 10 15 ((srcNinthCShort.flat).take 15360) ((wGninthN3pXHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem wGninthN3pXHT_check1 :
    shortCheckPk wGninthN3pXHD 10 15 (((srcNinthCShort.flat).drop 15360).take 15360)
        (((wGninthN3pXHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem wGninthN3pXHT_check2 :
    shortCheckPk wGninthN3pXHD 10 15 ((((srcNinthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN3pXHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem wGninthN3pXHT_check3 :
    shortCheckPk wGninthN3pXHD 10 15 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).take 15360) (((((wGninthN3pXHT).drop 15360).drop 15360).drop 15360).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 4). -/
theorem wGninthN3pXHT_check4 :
    shortCheckPk wGninthN3pXHD 10 1 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).drop 15360) (((((wGninthN3pXHT).drop 15360).drop 15360).drop 15360).drop 15360) =
        true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem wGninthN3pXHT_check : shortCheckF wGninthN3pXHD srcNinthCShort.flat wGninthN3pXHT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN3pXHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN3pXHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN3pXHT_check2)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN3pXHT_check3)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN3pXHT_check4))))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGninthN3pXT_labels : wGninthN3pXHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGninthN3pXGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGninthN3pXH_growth : tensorWordGrowthAll wGninthN3pXH * 15 = 3840 := by decide

/-- The word bound of the target word. -/
theorem wGninthN3pXG_growth : tensorWordGrowthAll wGninthN3pXG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem wGninthN3pXL_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN3pXH)
    (generatedAxisGlobalTwelveRepresentative 8)) = wGninthN3pXL.real := by
  have hT := (tensorPlanF_actual wGninthN3pXHPlan wGninthN3pXHPlan_ok (ninthSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN3pXHPlan_word, wGninthN3pXH_growth]; norm_num) 32).2
  rw [wGninthN3pXHPlan_word] at hT
  exact IdentVec.word_actual (ninthSrcVecL 64) wGninthN3pXHW wGninthN3pXH_check wGninthN3pXHD
      wGninthN3pXD_ok.1 wGninthN3pXHD_cols
    wGninthN3pXHD_rows wGninthN3pXHT wGninthN3pXHT_check _ hT _ (ninthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
