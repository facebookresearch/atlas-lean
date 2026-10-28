/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1pXData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Ninth[1]+ <-> Twelfth[25]-
(record gninth:N1+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGninthN1pXChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGninthN1pXH : List IdentLetter := wGninthN1pXHW.map Prod.fst

/-- The target word. -/
def wGninthN1pXG : List IdentLetter := wGninthN1pXGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN1pXG`. -/
def wGninthN1pXGPlan : List TPlan :=
  [.letter (.qel (qmElt (2132343, false))),
    .letter (.sign 2006 0),
    .run
      [(0, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, true),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, true), (1, false), (0, false), (1, false), (0, true), (0, true), (1, false)]
      [.trans 2 3, .trans 5 9, .trans 0 2, .trans 10 0, .trans 0 4, .trans 8 10, .trans 3 0,
        .trans 2 1, .trans 3 11, .trans 5 6, .trans 5 1, .trans 9 1, .trans 1 4,
        .trans 4 7, .trans 7 6, .trans 1 2, .trans 1 3, .trans 3 6, .trans 6 7,
        .trans 6 0, .trans 0 2, .trans 0 9, .trans 2 4, .trans 2 7, .trans 2 11,
        .trans 5 10, .trans 7 5, .trans 7 8, .trans 7 10, .trans 8 2, .trans 8 4,
        .trans 8 5, .trans 8 7, .trans 8 10, .trans 8 11, .trans 9 4, .trans 9 5,
        .trans 9 10, .trans 10 0, .trans 10 2, .trans 10 7, .trans 10 9],
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
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN1pXGPlan_word : planWord wGninthN1pXGPlan = wGninthN1pXG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN1pXGPlan_ok : planOk wGninthN1pXGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGninthN1pXHX : List SVec := tensorWordAll 64 wGninthN1pXH (ninthSrcXL 64)

/-- The packed tensor of the target image. -/
def wGninthN1pXGX : List SVec := tensorPlanF 64 wGninthN1pXGPlan (twelfthSrcXW 64)

/-- The representation of the source image. -/
def wGninthN1pXL : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN1pXH, ShortData.ofList wGninthN1pXHT, (1 / 128),
    tensorRat 64 wGninthN1pXHX ((tensorWordDenAll wGninthN1pXH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGninthN1pXW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet wGninthN1pXG, ShortData.ofList wGninthN1pXGT, (1 / 128),
    tensorRat 64 wGninthN1pXGX ((tensorWordDenAll wGninthN1pXG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGninthN1pXH_check : wGninthN1pXHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGninthN1pXD_ok : wGninthN1pXHD.ok = true ∧ wGninthN1pXGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGninthN1pXHD_cols : ∀ i : Fin 24, qmWordP (wGninthN1pXHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN1pXHD.colsP i.val, wGninthN1pXHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGninthN1pXHD_rows : ∀ i : Fin 24,
    fld 24 wGninthN1pXHD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN1pXHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem wGninthN1pXHT_check0 :
    shortCheckPk wGninthN1pXHD 10 15 ((srcNinthCShort.flat).take 15360) ((wGninthN1pXHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem wGninthN1pXHT_check1 :
    shortCheckPk wGninthN1pXHD 10 15 (((srcNinthCShort.flat).drop 15360).take 15360)
        (((wGninthN1pXHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem wGninthN1pXHT_check2 :
    shortCheckPk wGninthN1pXHD 10 15 ((((srcNinthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN1pXHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem wGninthN1pXHT_check3 :
    shortCheckPk wGninthN1pXHD 10 15 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).take 15360) (((((wGninthN1pXHT).drop 15360).drop 15360).drop 15360).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 4). -/
theorem wGninthN1pXHT_check4 :
    shortCheckPk wGninthN1pXHD 10 1 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).drop 15360) (((((wGninthN1pXHT).drop 15360).drop 15360).drop 15360).drop 15360) =
        true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem wGninthN1pXHT_check : shortCheckF wGninthN1pXHD srcNinthCShort.flat wGninthN1pXHT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1pXHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1pXHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1pXHT_check2)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1pXHT_check3)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN1pXHT_check4))))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGninthN1pXT_labels : wGninthN1pXHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGninthN1pXGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGninthN1pXH_growth : tensorWordGrowthAll wGninthN1pXH * 15 = 3840 := by decide

/-- The word bound of the target word. -/
theorem wGninthN1pXG_growth : tensorWordGrowthAll wGninthN1pXG * 15 = 515396075520 := by decide

/-- The coordinates of the source image. -/
theorem wGninthN1pXL_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN1pXH)
    (generatedAxisGlobalTwelveRepresentative 8)) = wGninthN1pXL.real := by
  have hT := (tensorWordAll_actual wGninthN1pXH (ninthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wGninthN1pXH_growth]; norm_num) 32).2
  exact IdentVec.word_actual (ninthSrcVecL 64) wGninthN1pXHW wGninthN1pXH_check wGninthN1pXHD
      wGninthN1pXD_ok.1 wGninthN1pXHD_cols
    wGninthN1pXHD_rows wGninthN1pXHT wGninthN1pXHT_check _ hT _ (ninthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
