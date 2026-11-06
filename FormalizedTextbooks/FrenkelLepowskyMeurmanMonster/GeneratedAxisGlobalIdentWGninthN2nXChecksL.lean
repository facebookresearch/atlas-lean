/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN2nXData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Ninth[3]- <-> Tenth[50]+
(record gninth:N2-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGninthN2nXChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGninthN2nXH : List IdentLetter := wGninthN2nXHW.map Prod.fst

/-- The target word. -/
def wGninthN2nXG : List IdentLetter := wGninthN2nXGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN2nXH`. -/
def wGninthN2nXHPlan : List TPlan :=
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
theorem wGninthN2nXHPlan_word : planWord wGninthN2nXHPlan = wGninthN2nXH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN2nXHPlan_ok : planOk wGninthN2nXHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN2nXG`. -/
def wGninthN2nXGPlan : List TPlan :=
  [.letter (.qel (qmElt (907184, false))),
    .letter (.sign 1356 0),
    .run
      [(0, true), (0, true), (1, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, true), (0, true),
        (1, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, false),
        (1, false), (0, true), (1, false), (0, false), (0, false), (0, false),
        (1, false), (0, true), (0, true), (0, true), (1, false)]
      [.trans 1 0, .trans 0 1, .trans 0 3, .trans 0 4, .trans 0 5, .trans 0 7, .trans 0 8,
        .trans 1 0, .trans 1 2, .trans 1 5, .trans 1 7, .trans 7 2, .trans 2 0,
        .trans 2 1, .trans 2 7, .trans 2 8, .trans 3 1, .trans 3 4, .trans 3 6,
        .trans 3 9, .trans 3 10, .trans 4 1, .trans 4 3, .trans 5 0, .trans 5 2,
        .trans 5 3, .trans 5 6, .trans 5 8, .trans 8 6, .trans 6 1, .trans 6 3,
        .trans 6 8, .trans 8 7, .trans 7 0, .trans 7 2, .trans 7 3, .trans 7 4,
        .trans 7 5, .trans 7 8, .trans 8 0, .trans 8 1, .trans 8 2, .trans 8 4,
        .trans 8 6, .trans 8 7, .trans 8 10, .trans 9 0, .trans 9 1, .trans 9 2,
        .trans 9 5, .trans 9 7, .trans 9 8, .trans 9 10, .trans 9 11, .trans 10 0,
        .trans 10 2, .trans 10 7, .trans 10 8, .trans 10 11],
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
theorem wGninthN2nXGPlan_word : planWord wGninthN2nXGPlan = wGninthN2nXG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN2nXGPlan_ok : planOk wGninthN2nXGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGninthN2nXHX : List SVec := tensorPlanF 64 wGninthN2nXHPlan (ninthSrcXL 64)

/-- The packed tensor of the target image. -/
def wGninthN2nXGX : List SVec := tensorPlanF 64 wGninthN2nXGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGninthN2nXL : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN2nXH, ShortData.ofList wGninthN2nXHT, (1 / 128),
    tensorRat 64 wGninthN2nXHX ((tensorWordDenAll wGninthN2nXH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGninthN2nXW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGninthN2nXG, ShortData.ofList wGninthN2nXGT, (1 / 128),
    tensorRat 64 wGninthN2nXGX ((tensorWordDenAll wGninthN2nXG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGninthN2nXH_check : wGninthN2nXHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGninthN2nXD_ok : wGninthN2nXHD.ok = true ∧ wGninthN2nXGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGninthN2nXHD_cols : ∀ i : Fin 24, qmWordP (wGninthN2nXHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN2nXHD.colsP i.val, wGninthN2nXHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGninthN2nXHD_rows : ∀ i : Fin 24,
    fld 24 wGninthN2nXHD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN2nXHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem wGninthN2nXHT_check0 :
    shortCheckPk wGninthN2nXHD 10 15 ((srcNinthCShort.flat).take 15360) ((wGninthN2nXHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem wGninthN2nXHT_check1 :
    shortCheckPk wGninthN2nXHD 10 15 (((srcNinthCShort.flat).drop 15360).take 15360)
        (((wGninthN2nXHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem wGninthN2nXHT_check2 :
    shortCheckPk wGninthN2nXHD 10 15 ((((srcNinthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN2nXHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem wGninthN2nXHT_check3 :
    shortCheckPk wGninthN2nXHD 10 15 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).take 15360) (((((wGninthN2nXHT).drop 15360).drop 15360).drop 15360).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 4). -/
theorem wGninthN2nXHT_check4 :
    shortCheckPk wGninthN2nXHD 10 1 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).drop 15360) (((((wGninthN2nXHT).drop 15360).drop 15360).drop 15360).drop 15360) =
        true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem wGninthN2nXHT_check : shortCheckF wGninthN2nXHD srcNinthCShort.flat wGninthN2nXHT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2nXHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2nXHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2nXHT_check2)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN2nXHT_check3)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN2nXHT_check4))))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGninthN2nXT_labels : wGninthN2nXHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGninthN2nXGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGninthN2nXH_growth : tensorWordGrowthAll wGninthN2nXH * 15 = 983040 := by decide

/-- The word bound of the target word. -/
theorem wGninthN2nXG_growth : tensorWordGrowthAll wGninthN2nXG * 15 = 33776997205278720 := by decide

/-- The coordinates of the source image. -/
theorem wGninthN2nXL_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN2nXH)
    (generatedAxisGlobalTwelveRepresentative 8)) = wGninthN2nXL.real := by
  have hT := (tensorPlanF_actual wGninthN2nXHPlan wGninthN2nXHPlan_ok (ninthSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN2nXHPlan_word, wGninthN2nXH_growth]; norm_num) 32).2
  rw [wGninthN2nXHPlan_word] at hT
  exact IdentVec.word_actual (ninthSrcVecL 64) wGninthN2nXHW wGninthN2nXH_check wGninthN2nXHD
      wGninthN2nXD_ok.1 wGninthN2nXHD_cols
    wGninthN2nXHD_rows wGninthN2nXHT wGninthN2nXHT_check _ hT _ (ninthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
