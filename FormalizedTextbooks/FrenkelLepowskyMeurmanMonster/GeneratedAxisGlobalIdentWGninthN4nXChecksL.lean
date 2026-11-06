/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN4nXData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Ninth[6]- <-> Tenth[74]-
(record gninth:N4-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGninthN4nXChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGninthN4nXH : List IdentLetter := wGninthN4nXHW.map Prod.fst

/-- The target word. -/
def wGninthN4nXG : List IdentLetter := wGninthN4nXGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN4nXH`. -/
def wGninthN4nXHPlan : List TPlan :=
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
theorem wGninthN4nXHPlan_word : planWord wGninthN4nXHPlan = wGninthN4nXH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN4nXHPlan_ok : planOk wGninthN4nXHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN4nXG`. -/
def wGninthN4nXGPlan : List TPlan :=
  [.letter (.qel (qmElt (9480400, true))),
    .letter (.sign 1805 0),
    .run
      [(1, false), (0, false), (0, false), (1, false), (0, false), (1, false), (0, true),
        (0, true), (1, false), (0, false), (0, false), (0, false), (1, false),
        (0, false), (0, false), (1, false), (0, true), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, false)]
      [.trans 0 1, .trans 5 4, .trans 6 0, .trans 0 5, .trans 3 8, .trans 2 7, .trans 6 10,
        .trans 10 6, .trans 9 2, .trans 9 8, .trans 4 7, .trans 5 0, .trans 7 0,
        .trans 8 1, .trans 7 1, .trans 1 7, .trans 4 10, .trans 10 9, .trans 9 1,
        .trans 0 9, .trans 7 2, .trans 1 8, .trans 2 3, .trans 2 9, .trans 9 0,
        .trans 0 2, .trans 8 2, .trans 2 8, .trans 6 0, .trans 6 2, .trans 6 8,
        .trans 8 0, .trans 8 6],
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
theorem wGninthN4nXGPlan_word : planWord wGninthN4nXGPlan = wGninthN4nXG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN4nXGPlan_ok : planOk wGninthN4nXGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGninthN4nXHX : List SVec := tensorPlanF 64 wGninthN4nXHPlan (ninthSrcXL 64)

/-- The packed tensor of the target image. -/
def wGninthN4nXGX : List SVec := tensorPlanF 64 wGninthN4nXGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGninthN4nXL : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN4nXH, ShortData.ofList wGninthN4nXHT, (1 / 128),
    tensorRat 64 wGninthN4nXHX ((tensorWordDenAll wGninthN4nXH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGninthN4nXW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGninthN4nXG, ShortData.ofList wGninthN4nXGT, (1 / 128),
    tensorRat 64 wGninthN4nXGX ((tensorWordDenAll wGninthN4nXG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGninthN4nXH_check : wGninthN4nXHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGninthN4nXD_ok : wGninthN4nXHD.ok = true ∧ wGninthN4nXGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGninthN4nXHD_cols : ∀ i : Fin 24, qmWordP (wGninthN4nXHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN4nXHD.colsP i.val, wGninthN4nXHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGninthN4nXHD_rows : ∀ i : Fin 24,
    fld 24 wGninthN4nXHD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN4nXHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem wGninthN4nXHT_check0 :
    shortCheckPk wGninthN4nXHD 10 15 ((srcNinthCShort.flat).take 15360) ((wGninthN4nXHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem wGninthN4nXHT_check1 :
    shortCheckPk wGninthN4nXHD 10 15 (((srcNinthCShort.flat).drop 15360).take 15360)
        (((wGninthN4nXHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem wGninthN4nXHT_check2 :
    shortCheckPk wGninthN4nXHD 10 15 ((((srcNinthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN4nXHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem wGninthN4nXHT_check3 :
    shortCheckPk wGninthN4nXHD 10 15 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).take 15360) (((((wGninthN4nXHT).drop 15360).drop 15360).drop 15360).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 4). -/
theorem wGninthN4nXHT_check4 :
    shortCheckPk wGninthN4nXHD 10 1 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).drop 15360) (((((wGninthN4nXHT).drop 15360).drop 15360).drop 15360).drop 15360) =
        true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem wGninthN4nXHT_check : shortCheckF wGninthN4nXHD srcNinthCShort.flat wGninthN4nXHT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4nXHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4nXHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4nXHT_check2)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN4nXHT_check3)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN4nXHT_check4))))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGninthN4nXT_labels : wGninthN4nXHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGninthN4nXGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGninthN4nXH_growth : tensorWordGrowthAll wGninthN4nXH * 15 = 3840 := by decide

/-- The word bound of the target word. -/
theorem wGninthN4nXG_growth : tensorWordGrowthAll wGninthN4nXG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem wGninthN4nXL_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN4nXH)
    (generatedAxisGlobalTwelveRepresentative 8)) = wGninthN4nXL.real := by
  have hT := (tensorPlanF_actual wGninthN4nXHPlan wGninthN4nXHPlan_ok (ninthSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN4nXHPlan_word, wGninthN4nXH_growth]; norm_num) 32).2
  rw [wGninthN4nXHPlan_word] at hT
  exact IdentVec.word_actual (ninthSrcVecL 64) wGninthN4nXHW wGninthN4nXH_check wGninthN4nXHD
      wGninthN4nXD_ok.1 wGninthN4nXHD_cols
    wGninthN4nXHD_rows wGninthN4nXHT wGninthN4nXHT_check _ hT _ (ninthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
