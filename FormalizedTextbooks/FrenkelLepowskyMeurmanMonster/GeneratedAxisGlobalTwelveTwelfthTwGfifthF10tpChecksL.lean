/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGfifthF10tpData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Fifth[10]+ <-> Twelfth[36]-
(record gfifth:F10t+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalTwelveTwelfthTwGfifthF10tpChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def twGfifthF10tpH : List IdentLetter := twGfifthF10tpHW.map Prod.fst

/-- The target word. -/
def twGfifthF10tpG : List IdentLetter := twGfifthF10tpGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `twGfifthF10tpH`. -/
def twGfifthF10tpHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, false), (0, false)]
      [.trans 6 2, .trans 10 5, .trans 1 6, .trans 1 7, .trans 5 4, .trans 0 11, .trans 0 9,
        .trans 7 8, .trans 9 10, .trans 10 1, .trans 8 10, .trans 0 7, .trans 5 11,
        .trans 1 3, .trans 3 8, .trans 8 10, .trans 1 6, .trans 6 4, .trans 4 0,
        .trans 0 7, .trans 0 3, .trans 2 8, .trans 8 7, .trans 8 11, .trans 7 4,
        .trans 5 9, .trans 0 1, .trans 9 5, .trans 4 1, .trans 1 9, .trans 4 6,
        .trans 6 5, .trans 5 2, .trans 6 9, .trans 5 8, .trans 9 10, .trans 8 10,
        .trans 10 2, .trans 2 3, .trans 3 11],
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem twGfifthF10tpHPlan_word : planWord twGfifthF10tpHPlan = twGfifthF10tpH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem twGfifthF10tpHPlan_ok : planOk twGfifthF10tpHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `twGfifthF10tpG`. -/
def twGfifthF10tpGPlan : List TPlan :=
  [.letter (.qel (qmElt (4607048, false))),
    .letter (.sign 916 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, true), (0, true), (0, true), (1, false), (0, false),
        (0, false), (1, false), (0, true), (1, false), (0, false), (0, false),
        (1, false), (0, true), (1, false), (0, false), (0, false), (1, true), (0, true),
        (0, true), (1, true), (0, true), (1, true), (0, true), (0, true), (1, true),
        (0, true), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false),
        (0, false), (1, true), (0, false), (1, true), (0, false), (0, false), (0, false),
        (1, false), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, false),
        (1, false), (0, true), (1, false), (0, true), (0, true), (0, true)]
      [.trans 1 9, .trans 10 1, .trans 8 4, .trans 8 10, .trans 9 1, .trans 3 11, .trans 9 2,
        .trans 2 0, .trans 6 5, .trans 3 2, .trans 6 7, .trans 0 1, .trans 6 10,
        .trans 0 3, .trans 3 8, .trans 5 11, .trans 8 5, .trans 10 3, .trans 5 3,
        .trans 3 5, .trans 8 7, .trans 1 0, .trans 0 7, .trans 7 6, .trans 0 2,
        .trans 2 3, .trans 6 4, .trans 3 9, .trans 4 8, .trans 8 4, .trans 4 11,
        .trans 9 8],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true), (0, true), (0, true), (1, true), (0, false), (0, false)]
      [.trans 10 11, .trans 1 10, .trans 3 5, .trans 2 1, .trans 1 6, .trans 4 3, .trans 7 2,
        .trans 6 4, .trans 8 0, .trans 0 1, .trans 2 8, .trans 10 2, .trans 1 4,
        .trans 4 2, .trans 2 3, .trans 10 8, .trans 8 1, .trans 1 10, .trans 8 7,
        .trans 5 7, .trans 7 3, .trans 10 6, .trans 3 0, .trans 0 8, .trans 6 11,
        .trans 10 9, .trans 0 3, .trans 4 0, .trans 0 4, .trans 7 6, .trans 7 11,
        .trans 1 0, .trans 3 0, .trans 3 1, .trans 3 5, .trans 3 8, .trans 6 9,
        .trans 8 6, .trans 8 9, .trans 9 0, .trans 9 1, .trans 9 3, .trans 9 5,
        .trans 9 6, .trans 9 8]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem twGfifthF10tpGPlan_word : planWord twGfifthF10tpGPlan = twGfifthF10tpG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem twGfifthF10tpGPlan_ok : planOk twGfifthF10tpGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def twGfifthF10tpHX : List SVec := tensorPlanF 80 twGfifthF10tpHPlan (fifthSrcXW 80)

/-- The packed tensor of the target image. -/
def twGfifthF10tpGX : List SVec := tensorPlanF 80 twGfifthF10tpGPlan (twelfthSrcXW 80)

/-- The representation of the source image. -/
def twGfifthF10tpL : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet twGfifthF10tpH, ShortData.ofList twGfifthF10tpHT, 1 / 16,
    tensorRat 80 twGfifthF10tpHX ((tensorWordDenAll twGfifthF10tpH : ℚ) * 1)⟩

/-- The representation of the target image. -/
def twGfifthF10tpW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet twGfifthF10tpG, ShortData.ofList twGfifthF10tpGT, (1 /
      128),
    tensorRat 80 twGfifthF10tpGX ((tensorWordDenAll twGfifthF10tpG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem twGfifthF10tpH_check : twGfifthF10tpHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem twGfifthF10tpD_ok : twGfifthF10tpHD.ok = true ∧ twGfifthF10tpGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem twGfifthF10tpHD_cols : ∀ i : Fin 24, qmWordP (twGfifthF10tpHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 twGfifthF10tpHD.colsP i.val, twGfifthF10tpHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem twGfifthF10tpHD_rows : ∀ i : Fin 24,
    fld 24 twGfifthF10tpHD.rowsP i.val = rowsOf (fun j => fld 24 twGfifthF10tpHD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem twGfifthF10tpHT_check : shortCheckF twGfifthF10tpHD fifthSrcShort.flat twGfifthF10tpHT =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem twGfifthF10tpT_labels : twGfifthF10tpHT.all (fun p => decide (p.1 < 98280)) = true ∧
    twGfifthF10tpGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem twGfifthF10tpH_growth : tensorWordGrowthAll twGfifthF10tpH * 64 = 274877906944 := by decide

/-- The word bound of the target word. -/
theorem twGfifthF10tpG_growth : tensorWordGrowthAll twGfifthF10tpG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem twGfifthF10tpL_actual : griessConwayEncode (rhoLocal (identWordLocal twGfifthF10tpH)
    (generatedAxisGlobalTwelveRepresentative 4)) = twGfifthF10tpL.real := by
  have hT := (tensorPlanF_actual twGfifthF10tpHPlan twGfifthF10tpHPlan_ok (fifthSrcXW_bnd (w :=
      80) (by norm_num))
    (by rw [twGfifthF10tpHPlan_word, twGfifthF10tpH_growth]; norm_num) 1).2
  rw [twGfifthF10tpHPlan_word] at hT
  exact IdentVec.word_actual (fifthSrcVecW 80) twGfifthF10tpHW twGfifthF10tpH_check
      twGfifthF10tpHD twGfifthF10tpD_ok.1 twGfifthF10tpHD_cols
    twGfifthF10tpHD_rows twGfifthF10tpHT twGfifthF10tpHT_check _ hT _ (fifthSrcW_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
