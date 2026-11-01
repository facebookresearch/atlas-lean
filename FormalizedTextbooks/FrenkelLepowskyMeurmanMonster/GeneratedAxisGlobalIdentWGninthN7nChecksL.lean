/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Fifth[4]+ <-> Ninth[12]-
(record gninth:N7-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGninthN7nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGninthN7nH : List IdentLetter := wGninthN7nHW.map Prod.fst

/-- The target word. -/
def wGninthN7nG : List IdentLetter := wGninthN7nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN7nH`. -/
def wGninthN7nHPlan : List TPlan :=
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
        .trans 8 2, .trans 8 4, .trans 8 11],
    .letter (.xi),
    .run
      [(0, false), (0, false)]
      [.trans 9 2, .trans 0 11, .trans 0 4, .trans 4 9, .trans 4 6, .trans 7 8, .trans 8 3,
        .trans 3 11, .trans 10 4, .trans 4 1, .trans 6 7, .trans 0 2, .trans 7 6,
        .trans 7 1, .trans 0 7, .trans 7 0, .trans 1 11, .trans 1 8, .trans 8 2,
        .trans 3 2, .trans 2 8, .trans 4 7, .trans 4 8, .trans 5 10, .trans 6 10,
        .trans 7 9, .trans 8 3, .trans 8 9, .trans 9 11, .trans 10 3, .trans 10 4,
        .trans 10 5, .trans 10 6, .trans 10 7, .trans 10 8],
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
theorem wGninthN7nHPlan_word : planWord wGninthN7nHPlan = wGninthN7nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN7nHPlan_ok : planOk wGninthN7nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN7nG`. -/
def wGninthN7nGPlan : List TPlan :=
  [.letter (.qel (qmElt (14985297, false))),
    .letter (.sign 1570 0),
    .run
      [(0, true), (1, false), (0, false), (0, false), (1, false), (0, true), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, true), (0, true), (1, false),
        (0, true), (1, false), (0, true), (0, true), (1, false), (0, true)]
      [.trans 10 8, .trans 10 9, .trans 3 7, .trans 7 5, .trans 6 10, .trans 3 1, .trans 8 3,
        .trans 6 4, .trans 4 1, .trans 1 3, .trans 5 6, .trans 3 1, .trans 10 7,
        .trans 6 1, .trans 1 2, .trans 10 0, .trans 2 6, .trans 0 10, .trans 10 0,
        .trans 2 1, .trans 7 4, .trans 1 5, .trans 4 5, .trans 4 6, .trans 5 7,
        .trans 7 10, .trans 9 4, .trans 9 5, .trans 9 6, .trans 10 4, .trans 10 5,
        .trans 10 6, .trans 10 8, .trans 10 9],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true), (0, true), (1, true), (0, false), (1, true)]
      [.trans 6 11, .trans 3 8, .trans 3 9, .trans 3 7, .trans 4 5, .trans 4 6, .trans 4 10,
        .trans 10 0, .trans 1 11, .trans 10 3, .trans 7 1, .trans 3 6, .trans 1 6,
        .trans 6 9, .trans 6 1, .trans 1 3, .trans 1 7, .trans 1 11, .trans 11 10,
        .trans 0 11, .trans 10 1, .trans 1 10, .trans 2 0, .trans 2 7, .trans 2 11,
        .trans 3 0, .trans 3 2, .trans 3 7, .trans 3 8, .trans 3 9, .trans 3 11,
        .trans 4 8, .trans 5 4, .trans 5 8, .trans 5 9, .trans 7 8, .trans 8 0,
        .trans 8 2, .trans 8 3, .trans 8 7, .trans 8 9, .trans 8 11, .trans 9 1,
        .trans 9 10, .trans 10 4, .trans 10 5, .trans 10 7, .trans 10 9, .trans 10 11,
        .trans 11 1],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, true)]
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
theorem wGninthN7nGPlan_word : planWord wGninthN7nGPlan = wGninthN7nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN7nGPlan_ok : planOk wGninthN7nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGninthN7nHX : List SVec := tensorPlanF 64 wGninthN7nHPlan (ninthSrcXL 64)

/-- The packed tensor of the target image. -/
def wGninthN7nGX : List SVec := tensorPlanF 64 wGninthN7nGPlan (fifthSrcXW 64)

/-- The representation of the source image. -/
def wGninthN7nL : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN7nH, ShortData.ofList wGninthN7nHT, (1 / 128),
    tensorRat 64 wGninthN7nHX ((tensorWordDenAll wGninthN7nH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGninthN7nW : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet wGninthN7nG, ShortData.ofList wGninthN7nGT, 1 / 16,
    tensorRat 64 wGninthN7nGX ((tensorWordDenAll wGninthN7nG : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGninthN7nH_check : wGninthN7nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGninthN7nD_ok : wGninthN7nHD.ok = true ∧ wGninthN7nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGninthN7nHD_cols : ∀ i : Fin 24, qmWordP (wGninthN7nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN7nHD.colsP i.val, wGninthN7nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGninthN7nHD_rows : ∀ i : Fin 24,
    fld 24 wGninthN7nHD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN7nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem wGninthN7nHT_check0 :
    shortCheckPk wGninthN7nHD 10 15 ((srcNinthCShort.flat).take 15360) ((wGninthN7nHT).take 15360)
        = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem wGninthN7nHT_check1 :
    shortCheckPk wGninthN7nHD 10 15 (((srcNinthCShort.flat).drop 15360).take 15360)
        (((wGninthN7nHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem wGninthN7nHT_check2 :
    shortCheckPk wGninthN7nHD 10 15 ((((srcNinthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN7nHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem wGninthN7nHT_check3 :
    shortCheckPk wGninthN7nHD 10 15 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).take 15360) (((((wGninthN7nHT).drop 15360).drop 15360).drop 15360).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 4). -/
theorem wGninthN7nHT_check4 :
    shortCheckPk wGninthN7nHD 10 1 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).drop 15360) (((((wGninthN7nHT).drop 15360).drop 15360).drop 15360).drop 15360) =
        true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem wGninthN7nHT_check : shortCheckF wGninthN7nHD srcNinthCShort.flat wGninthN7nHT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN7nHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN7nHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN7nHT_check2)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN7nHT_check3)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN7nHT_check4))))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGninthN7nT_labels : wGninthN7nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGninthN7nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGninthN7nH_growth : tensorWordGrowthAll wGninthN7nH * 15 = 64424509440 := by decide

/-- The word bound of the target word. -/
theorem wGninthN7nG_growth : tensorWordGrowthAll wGninthN7nG * 64 = 2199023255552 := by decide

/-- The coordinates of the source image. -/
theorem wGninthN7nL_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN7nH)
    (generatedAxisGlobalTwelveRepresentative 8)) = wGninthN7nL.real := by
  have hT := (tensorPlanF_actual wGninthN7nHPlan wGninthN7nHPlan_ok (ninthSrcXL_bnd (w := 64) (by
      norm_num))
    (by rw [wGninthN7nHPlan_word, wGninthN7nH_growth]; norm_num) 32).2
  rw [wGninthN7nHPlan_word] at hT
  exact IdentVec.word_actual (ninthSrcVecL 64) wGninthN7nHW wGninthN7nH_check wGninthN7nHD
      wGninthN7nD_ok.1 wGninthN7nHD_cols
    wGninthN7nHD_rows wGninthN7nHT wGninthN7nHT_check _ hT _ (ninthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
