/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4pXData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Ninth[6]+ <-> Tenth[74]-
(record gninth:N4+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGninthN4pXChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGninthN4pXH : List IdentLetter := wGninthN4pXHW.map Prod.fst

/-- The target word. -/
def wGninthN4pXG : List IdentLetter := wGninthN4pXGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN4pXH`. -/
def wGninthN4pXHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(0, false), (0, false)]
      [.trans 9 2, .trans 0 11, .trans 0 4, .trans 4 9, .trans 4 6, .trans 7 8, .trans 8 3,
        .trans 3 11, .trans 10 4, .trans 4 1, .trans 6 7, .trans 0 2, .trans 7 6,
        .trans 7 1, .trans 0 7, .trans 7 0, .trans 1 11, .trans 1 8, .trans 8 2,
        .trans 3 2, .trans 2 8, .trans 4 7, .trans 4 8, .trans 5 10, .trans 6 10,
        .trans 7 9, .trans 8 3, .trans 8 9, .trans 9 11, .trans 10 3, .trans 10 4,
        .trans 10 5, .trans 10 6, .trans 10 7, .trans 10 8]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN4pXHPlan_word : planWord wGninthN4pXHPlan = wGninthN4pXH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN4pXHPlan_ok : planOk wGninthN4pXHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN4pXG`. -/
def wGninthN4pXGPlan : List TPlan :=
  [.letter (.qel (qmElt (4534651, false))),
    .letter (.sign 344 0),
    .run
      [(1, false), (0, true), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, true), (1, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, true), (1, false), (0, false)]
      [.trans 5 7, .trans 4 5, .trans 10 5, .trans 0 5, .trans 3 8, .trans 8 2, .trans 6 10,
        .trans 2 9, .trans 10 6, .trans 2 1, .trans 10 3, .trans 10 7, .trans 7 4,
        .trans 4 0, .trans 0 1, .trans 5 0, .trans 0 4, .trans 4 8, .trans 4 10,
        .trans 10 1, .trans 1 8, .trans 1 0, .trans 10 2, .trans 0 3, .trans 3 9,
        .trans 9 7, .trans 9 2, .trans 2 3, .trans 8 3, .trans 3 8, .trans 6 2,
        .trans 6 8, .trans 8 2, .trans 8 3, .trans 8 6],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, true), (0, true), (0, true)]
      [.trans 2 4, .trans 0 10, .trans 2 3, .trans 7 2, .trans 3 8, .trans 8 7, .trans 5 10,
        .trans 4 0, .trans 5 1, .trans 2 11, .trans 2 0, .trans 6 0, .trans 7 0,
        .trans 0 11, .trans 0 2, .trans 5 3, .trans 0 6, .trans 4 9, .trans 3 4,
        .trans 3 9, .trans 9 5, .trans 5 8, .trans 8 2, .trans 8 11, .trans 2 3,
        .trans 5 1, .trans 1 2, .trans 1 9, .trans 9 10, .trans 10 8, .trans 2 4,
        .trans 3 11, .trans 4 6, .trans 4 7, .trans 7 8, .trans 8 10, .trans 10 2,
        .trans 10 3, .trans 10 4, .trans 10 6, .trans 10 7, .trans 10 8, .trans 10 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN4pXGPlan_word : planWord wGninthN4pXGPlan = wGninthN4pXG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN4pXGPlan_ok : planOk wGninthN4pXGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGninthN4pXHX : List SVec := tensorPlanF 64 wGninthN4pXHPlan (ninthSrcXL 64)

/-- The packed tensor of the target image. -/
def wGninthN4pXGX : List SVec := tensorPlanF 64 wGninthN4pXGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGninthN4pXL : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN4pXH, ShortData.ofList wGninthN4pXHT, (1 / 128),
    tensorRat 64 wGninthN4pXHX ((tensorWordDenAll wGninthN4pXH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGninthN4pXW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGninthN4pXG, ShortData.ofList wGninthN4pXGT, (1 / 128),
    tensorRat 64 wGninthN4pXGX ((tensorWordDenAll wGninthN4pXG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGninthN4pXH_check : wGninthN4pXHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGninthN4pXD_ok : wGninthN4pXHD.ok = true ∧ wGninthN4pXGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGninthN4pXHD_cols : ∀ i : Fin 24, qmWordP (wGninthN4pXHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN4pXHD.colsP i.val, wGninthN4pXHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGninthN4pXHD_rows : ∀ i : Fin 24,
    fld 24 wGninthN4pXHD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN4pXHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem wGninthN4pXHT_check0 :
    shortCheckPk wGninthN4pXHD 10 15 ((srcNinthCShort.flat).take 15360) ((wGninthN4pXHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem wGninthN4pXHT_check1 :
    shortCheckPk wGninthN4pXHD 10 15 (((srcNinthCShort.flat).drop 15360).take 15360)
        (((wGninthN4pXHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem wGninthN4pXHT_check2 :
    shortCheckPk wGninthN4pXHD 10 15 ((((srcNinthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN4pXHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem wGninthN4pXHT_check3 :
    shortCheckPk wGninthN4pXHD 10 15 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).take 15360) (((((wGninthN4pXHT).drop 15360).drop 15360).drop 15360).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 4). -/
theorem wGninthN4pXHT_check4 :
    shortCheckPk wGninthN4pXHD 10 1 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).drop 15360) (((((wGninthN4pXHT).drop 15360).drop 15360).drop 15360).drop 15360) =
        true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem wGninthN4pXHT_check : shortCheckF wGninthN4pXHD srcNinthCShort.flat wGninthN4pXHT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4pXHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4pXHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4pXHT_check2)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4pXHT_check3)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN4pXHT_check4))))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGninthN4pXT_labels : wGninthN4pXHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGninthN4pXGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGninthN4pXH_growth : tensorWordGrowthAll wGninthN4pXH * 15 = 3840 := by decide

/-- The word bound of the target word. -/
theorem wGninthN4pXG_growth : tensorWordGrowthAll wGninthN4pXG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem wGninthN4pXL_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN4pXH)
    (generatedAxisGlobalTwelveRepresentative 8)) = wGninthN4pXL.real := by
  have hT := (tensorPlanF_actual wGninthN4pXHPlan wGninthN4pXHPlan_ok (ninthSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN4pXHPlan_word, wGninthN4pXH_growth]; norm_num) 32).2
  rw [wGninthN4pXHPlan_word] at hT
  exact IdentVec.word_actual (ninthSrcVecL 64) wGninthN4pXHW wGninthN4pXH_check wGninthN4pXHD
      wGninthN4pXD_ok.1 wGninthN4pXHD_cols
    wGninthN4pXHD_rows wGninthN4pXHT wGninthN4pXHT_check _ hT _ (ninthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
