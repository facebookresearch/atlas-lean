/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN5nXData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Ninth[7]- <-> Ninth[7]-
(record gninth:N5-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGninthN5nXChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGninthN5nXH : List IdentLetter := wGninthN5nXHW.map Prod.fst

/-- The target word. -/
def wGninthN5nXG : List IdentLetter := wGninthN5nXGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN5nXH`. -/
def wGninthN5nXHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(1, false), (0, true)]
      [.trans 9 5, .trans 6 1, .trans 10 6, .trans 8 7, .trans 10 4, .trans 0 6, .trans 0 11,
        .trans 7 2, .trans 2 9, .trans 2 8, .trans 8 10, .trans 6 0, .trans 6 9,
        .trans 4 7, .trans 7 8, .trans 5 8, .trans 8 5, .trans 0 10, .trans 9 10,
        .trans 0 3, .trans 5 3, .trans 10 2, .trans 0 6, .trans 10 3, .trans 3 11,
        .trans 3 5, .trans 5 0, .trans 5 1, .trans 1 4, .trans 1 11, .trans 0 8,
        .trans 0 9, .trans 0 11, .trans 2 7, .trans 2 11, .trans 4 2, .trans 4 7,
        .trans 4 11, .trans 7 0, .trans 7 6, .trans 7 8, .trans 7 9, .trans 7 11,
        .trans 8 2, .trans 8 4, .trans 8 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN5nXHPlan_word : planWord wGninthN5nXHPlan = wGninthN5nXH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN5nXHPlan_ok : planOk wGninthN5nXHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN5nXG`. -/
def wGninthN5nXGPlan : List TPlan :=
  [.letter (.qel (qmElt (13228044, false))),
    .letter (.sign 1081 0),
    .run
      [(0, false), (0, false), (0, false), (1, false), (0, true), (1, false), (0, true),
        (0, true), (0, true), (1, false), (0, false), (1, false), (0, true), (1, false),
        (0, false), (0, false), (0, false), (1, false), (0, false), (1, false),
        (0, true), (0, true), (0, true)]
      [.trans 3 2, .trans 2 3, .trans 3 2, .trans 5 4, .trans 4 5, .trans 5 4, .trans 7 6,
        .trans 6 7, .trans 7 6, .trans 9 8, .trans 8 9, .trans 9 8],
    .letter (.xi),
    .run
      [(1, false), (0, true)]
      [.trans 9 5, .trans 6 1, .trans 10 6, .trans 8 7, .trans 10 4, .trans 0 6, .trans 0 11,
        .trans 7 2, .trans 2 9, .trans 2 8, .trans 8 10, .trans 6 0, .trans 6 9,
        .trans 4 7, .trans 7 8, .trans 5 8, .trans 8 5, .trans 0 10, .trans 9 10,
        .trans 0 3, .trans 5 3, .trans 10 2, .trans 0 6, .trans 10 3, .trans 3 11,
        .trans 3 5, .trans 5 0, .trans 5 1, .trans 1 4, .trans 1 11, .trans 0 8,
        .trans 0 9, .trans 0 11, .trans 2 7, .trans 2 11, .trans 4 2, .trans 4 7,
        .trans 4 11, .trans 7 0, .trans 7 6, .trans 7 8, .trans 7 9, .trans 7 11,
        .trans 8 2, .trans 8 4, .trans 8 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN5nXGPlan_word : planWord wGninthN5nXGPlan = wGninthN5nXG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN5nXGPlan_ok : planOk wGninthN5nXGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGninthN5nXHX : List SVec := tensorPlanF 64 wGninthN5nXHPlan (ninthSrcXL 64)

/-- The packed tensor of the target image. -/
def wGninthN5nXGX : List SVec := tensorPlanF 64 wGninthN5nXGPlan (ninthSrcXL 64)

/-- The representation of the source image. -/
def wGninthN5nXL : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN5nXH, ShortData.ofList wGninthN5nXHT, (1 / 128),
    tensorRat 64 wGninthN5nXHX ((tensorWordDenAll wGninthN5nXH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGninthN5nXW : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN5nXG, ShortData.ofList wGninthN5nXGT, (1 / 128),
    tensorRat 64 wGninthN5nXGX ((tensorWordDenAll wGninthN5nXG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGninthN5nXH_check : wGninthN5nXHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGninthN5nXD_ok : wGninthN5nXHD.ok = true ∧ wGninthN5nXGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGninthN5nXHD_cols : ∀ i : Fin 24, qmWordP (wGninthN5nXHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN5nXHD.colsP i.val, wGninthN5nXHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGninthN5nXHD_rows : ∀ i : Fin 24,
    fld 24 wGninthN5nXHD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN5nXHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem wGninthN5nXHT_check0 :
    shortCheckPk wGninthN5nXHD 10 15 ((srcNinthCShort.flat).take 15360) ((wGninthN5nXHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem wGninthN5nXHT_check1 :
    shortCheckPk wGninthN5nXHD 10 15 (((srcNinthCShort.flat).drop 15360).take 15360)
        (((wGninthN5nXHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem wGninthN5nXHT_check2 :
    shortCheckPk wGninthN5nXHD 10 15 ((((srcNinthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN5nXHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem wGninthN5nXHT_check3 :
    shortCheckPk wGninthN5nXHD 10 15 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).take 15360) (((((wGninthN5nXHT).drop 15360).drop 15360).drop 15360).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 4). -/
theorem wGninthN5nXHT_check4 :
    shortCheckPk wGninthN5nXHD 10 1 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).drop 15360) (((((wGninthN5nXHT).drop 15360).drop 15360).drop 15360).drop 15360) =
        true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem wGninthN5nXHT_check : shortCheckF wGninthN5nXHD srcNinthCShort.flat wGninthN5nXHT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN5nXHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN5nXHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN5nXHT_check2)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN5nXHT_check3)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN5nXHT_check4))))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGninthN5nXT_labels : wGninthN5nXHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGninthN5nXGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGninthN5nXH_growth : tensorWordGrowthAll wGninthN5nXH * 15 = 3840 := by decide

/-- The word bound of the target word. -/
theorem wGninthN5nXG_growth : tensorWordGrowthAll wGninthN5nXG * 15 = 30720 := by decide

/-- The coordinates of the source image. -/
theorem wGninthN5nXL_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN5nXH)
    (generatedAxisGlobalTwelveRepresentative 8)) = wGninthN5nXL.real := by
  have hT := (tensorPlanF_actual wGninthN5nXHPlan wGninthN5nXHPlan_ok (ninthSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN5nXHPlan_word, wGninthN5nXH_growth]; norm_num) 32).2
  rw [wGninthN5nXHPlan_word] at hT
  exact IdentVec.word_actual (ninthSrcVecL 64) wGninthN5nXHW wGninthN5nXH_check wGninthN5nXHD
      wGninthN5nXD_ok.1 wGninthN5nXHD_cols
    wGninthN5nXHD_rows wGninthN5nXHT wGninthN5nXHT_check _ hT _ (ninthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
