/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2pXData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Ninth[3]+ <-> Tenth[50]+
(record gninth:N2+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGninthN2pXChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGninthN2pXH : List IdentLetter := wGninthN2pXHW.map Prod.fst

/-- The target word. -/
def wGninthN2pXG : List IdentLetter := wGninthN2pXGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN2pXH`. -/
def wGninthN2pXHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(1, false)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN2pXHPlan_word : planWord wGninthN2pXHPlan = wGninthN2pXH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN2pXHPlan_ok : planOk wGninthN2pXHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN2pXG`. -/
def wGninthN2pXGPlan : List TPlan :=
  [.letter (.qel (qmElt (16541755, true))),
    .letter (.sign 1072 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, true), (0, true), (0, true), (1, false), (0, true), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, true), (1, false), (0, false),
        (1, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, false)]
      [.trans 9 10, .trans 5 4, .trans 1 0, .trans 1 9, .trans 9 6, .trans 1 2, .trans 6 9,
        .trans 5 6, .trans 6 2, .trans 8 10, .trans 3 9, .trans 8 5, .trans 9 8,
        .trans 8 3, .trans 8 9, .trans 9 0, .trans 5 1, .trans 2 1, .trans 1 8,
        .trans 8 4, .trans 8 7, .trans 0 1, .trans 1 0, .trans 8 10, .trans 10 6,
        .trans 10 5, .trans 6 4, .trans 4 3, .trans 2 7, .trans 3 1, .trans 5 7,
        .trans 7 1, .trans 7 2, .trans 7 3, .trans 7 5],
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
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11],
    .letter (.xi),
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN2pXGPlan_word : planWord wGninthN2pXGPlan = wGninthN2pXG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN2pXGPlan_ok : planOk wGninthN2pXGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGninthN2pXHX : List SVec := tensorPlanF 64 wGninthN2pXHPlan (ninthSrcXL 64)

/-- The packed tensor of the target image. -/
def wGninthN2pXGX : List SVec := tensorPlanF 64 wGninthN2pXGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGninthN2pXL : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN2pXH, ShortData.ofList wGninthN2pXHT, (1 / 128),
    tensorRat 64 wGninthN2pXHX ((tensorWordDenAll wGninthN2pXH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGninthN2pXW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGninthN2pXG, ShortData.ofList wGninthN2pXGT, (1 / 128),
    tensorRat 64 wGninthN2pXGX ((tensorWordDenAll wGninthN2pXG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGninthN2pXH_check : wGninthN2pXHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGninthN2pXD_ok : wGninthN2pXHD.ok = true ∧ wGninthN2pXGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGninthN2pXHD_cols : ∀ i : Fin 24, qmWordP (wGninthN2pXHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN2pXHD.colsP i.val, wGninthN2pXHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGninthN2pXHD_rows : ∀ i : Fin 24,
    fld 24 wGninthN2pXHD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN2pXHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem wGninthN2pXHT_check0 :
    shortCheckPk wGninthN2pXHD 10 15 ((srcNinthCShort.flat).take 15360) ((wGninthN2pXHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem wGninthN2pXHT_check1 :
    shortCheckPk wGninthN2pXHD 10 15 (((srcNinthCShort.flat).drop 15360).take 15360)
        (((wGninthN2pXHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem wGninthN2pXHT_check2 :
    shortCheckPk wGninthN2pXHD 10 15 ((((srcNinthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN2pXHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem wGninthN2pXHT_check3 :
    shortCheckPk wGninthN2pXHD 10 15 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).take 15360) (((((wGninthN2pXHT).drop 15360).drop 15360).drop 15360).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 4). -/
theorem wGninthN2pXHT_check4 :
    shortCheckPk wGninthN2pXHD 10 1 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).drop 15360) (((((wGninthN2pXHT).drop 15360).drop 15360).drop 15360).drop 15360) =
        true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem wGninthN2pXHT_check : shortCheckF wGninthN2pXHD srcNinthCShort.flat wGninthN2pXHT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2pXHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2pXHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2pXHT_check2)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2pXHT_check3)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN2pXHT_check4))))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGninthN2pXT_labels : wGninthN2pXHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGninthN2pXGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGninthN2pXH_growth : tensorWordGrowthAll wGninthN2pXH * 15 = 983040 := by decide

/-- The word bound of the target word. -/
theorem wGninthN2pXG_growth : tensorWordGrowthAll wGninthN2pXG * 15 = 33776997205278720 := by decide

/-- The coordinates of the source image. -/
theorem wGninthN2pXL_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN2pXH)
    (generatedAxisGlobalTwelveRepresentative 8)) = wGninthN2pXL.real := by
  have hT := (tensorPlanF_actual wGninthN2pXHPlan wGninthN2pXHPlan_ok (ninthSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN2pXHPlan_word, wGninthN2pXH_growth]; norm_num) 32).2
  rw [wGninthN2pXHPlan_word] at hT
  exact IdentVec.word_actual (ninthSrcVecL 64) wGninthN2pXHW wGninthN2pXH_check wGninthN2pXHD
      wGninthN2pXD_ok.1 wGninthN2pXHD_cols
    wGninthN2pXHD_rows wGninthN2pXHT wGninthN2pXHT_check _ hT _ (ninthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
