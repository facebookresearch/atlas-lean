/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Ninth[1]- <-> Tenth[33]+
(record gninth:N1-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGninthN1nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGninthN1nH : List IdentLetter := wGninthN1nHW.map Prod.fst

/-- The target word. -/
def wGninthN1nG : List IdentLetter := wGninthN1nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGninthN1nG`. -/
def wGninthN1nGPlan : List TPlan :=
  [.letter (.qel (qmElt (7776588, true))),
    .letter (.sign 476 0),
    .run
      [(0, true), (0, true), (1, false), (0, false), (0, false), (1, false), (0, true),
        (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (1, false),
        (0, false), (0, false), (1, false), (0, true), (0, true), (0, true), (1, false),
        (0, true), (0, true), (1, false), (0, true), (0, true), (1, false)]
      [.trans 0 2, .trans 0 11, .trans 1 2, .trans 1 3, .trans 1 11, .trans 3 2, .trans 2 0,
        .trans 2 1, .trans 2 3, .trans 2 11, .trans 3 0, .trans 7 4, .trans 4 1,
        .trans 4 2, .trans 4 7, .trans 6 5, .trans 5 0, .trans 5 1, .trans 5 4,
        .trans 5 6, .trans 8 6, .trans 6 4, .trans 6 8, .trans 9 7, .trans 7 0,
        .trans 7 2, .trans 7 5, .trans 7 9, .trans 8 2, .trans 8 6, .trans 8 7,
        .trans 8 9, .trans 8 11, .trans 9 1, .trans 9 4, .trans 9 7, .trans 9 11,
        .trans 10 3, .trans 10 4, .trans 10 8, .trans 10 9],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (1, true), (0, true), (0, true)]
      [.trans 8 3, .trans 4 3, .trans 6 5, .trans 5 10, .trans 8 7, .trans 4 2, .trans 8 4,
        .trans 8 6, .trans 2 9, .trans 5 6, .trans 3 8, .trans 2 8, .trans 4 8,
        .trans 8 11, .trans 5 0, .trans 4 0, .trans 0 1, .trans 0 10, .trans 1 9,
        .trans 0 7, .trans 2 5, .trans 9 0, .trans 3 6, .trans 10 8, .trans 9 4,
        .trans 8 3, .trans 9 11, .trans 10 4, .trans 8 6, .trans 6 2, .trans 7 3,
        .trans 6 5, .trans 3 2, .trans 2 4, .trans 2 1]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGninthN1nGPlan_word : planWord wGninthN1nGPlan = wGninthN1nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGninthN1nGPlan_ok : planOk wGninthN1nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGninthN1nHX : List SVec := tensorWordAll 64 wGninthN1nH (ninthSrcXL 64)

/-- The packed tensor of the target image. -/
def wGninthN1nGX : List SVec := tensorPlanF 64 wGninthN1nGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGninthN1nL : IdentVec :=
  ⟨srcNinthMat.act identSpatialAlphabet wGninthN1nH, ShortData.ofList wGninthN1nHT, (1 / 128),
    tensorRat 64 wGninthN1nHX ((tensorWordDenAll wGninthN1nH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGninthN1nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGninthN1nG, ShortData.ofList wGninthN1nGT, (1 / 128),
    tensorRat 64 wGninthN1nGX ((tensorWordDenAll wGninthN1nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGninthN1nH_check : wGninthN1nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGninthN1nD_ok : wGninthN1nHD.ok = true ∧ wGninthN1nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGninthN1nHD_cols : ∀ i : Fin 24, qmWordP (wGninthN1nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN1nHD.colsP i.val, wGninthN1nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGninthN1nHD_rows : ∀ i : Fin 24,
    fld 24 wGninthN1nHD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN1nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem wGninthN1nHT_check0 :
    shortCheckPk wGninthN1nHD 10 15 ((srcNinthCShort.flat).take 15360) ((wGninthN1nHT).take 15360)
        = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem wGninthN1nHT_check1 :
    shortCheckPk wGninthN1nHD 10 15 (((srcNinthCShort.flat).drop 15360).take 15360)
        (((wGninthN1nHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem wGninthN1nHT_check2 :
    shortCheckPk wGninthN1nHD 10 15 ((((srcNinthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN1nHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem wGninthN1nHT_check3 :
    shortCheckPk wGninthN1nHD 10 15 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).take 15360) (((((wGninthN1nHT).drop 15360).drop 15360).drop 15360).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 4). -/
theorem wGninthN1nHT_check4 :
    shortCheckPk wGninthN1nHD 10 1 (((((srcNinthCShort.flat).drop 15360).drop 15360).drop
        15360).drop 15360) (((((wGninthN1nHT).drop 15360).drop 15360).drop 15360).drop 15360) =
        true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem wGninthN1nHT_check : shortCheckF wGninthN1nHD srcNinthCShort.flat wGninthN1nHT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1nHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1nHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1nHT_check2)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1nHT_check3)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN1nHT_check4))))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGninthN1nT_labels : wGninthN1nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGninthN1nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGninthN1nH_growth : tensorWordGrowthAll wGninthN1nH * 15 = 3840 := by decide

/-- The word bound of the target word. -/
theorem wGninthN1nG_growth : tensorWordGrowthAll wGninthN1nG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem wGninthN1nL_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN1nH)
    (generatedAxisGlobalTwelveRepresentative 8)) = wGninthN1nL.real := by
  have hT := (tensorWordAll_actual wGninthN1nH (ninthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wGninthN1nH_growth]; norm_num) 32).2
  exact IdentVec.word_actual (ninthSrcVecL 64) wGninthN1nHW wGninthN1nH_check wGninthN1nHD
      wGninthN1nD_ok.1 wGninthN1nHD_cols
    wGninthN1nHD_rows wGninthN1nHT wGninthN1nHT_check _ hT _ (ninthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
