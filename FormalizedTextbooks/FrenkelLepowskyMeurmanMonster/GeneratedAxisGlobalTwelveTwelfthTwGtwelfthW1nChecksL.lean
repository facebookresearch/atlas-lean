/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Twelfth[1]- <-> Twelfth[1]+
(record gtwelfth:W1-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def twGtwelfthW1nH : List IdentLetter := twGtwelfthW1nHW.map Prod.fst

/-- The target word. -/
def twGtwelfthW1nG : List IdentLetter := twGtwelfthW1nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `twGtwelfthW1nH`. -/
def twGtwelfthW1nHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true)]
      [.trans 3 11, .trans 7 6, .trans 4 5, .trans 11 2, .trans 10 3, .trans 4 1, .trans 1 8,
        .trans 9 7, .trans 6 10, .trans 10 9, .trans 3 7, .trans 6 2, .trans 10 11,
        .trans 7 4, .trans 11 4, .trans 10 8, .trans 5 1, .trans 1 9, .trans 4 2,
        .trans 2 3, .trans 9 11, .trans 8 0, .trans 2 0, .trans 5 6, .trans 7 9,
        .trans 9 8, .trans 8 3, .trans 8 11, .trans 8 10, .trans 8 7, .trans 0 5,
        .trans 1 0, .trans 1 5, .trans 3 4, .trans 4 2, .trans 4 7, .trans 4 9,
        .trans 5 6, .trans 5 11, .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 3,
        .trans 6 4, .trans 6 7, .trans 6 9, .trans 9 10, .trans 11 2, .trans 11 4,
        .trans 11 7, .trans 11 9, .trans 11 10]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem twGtwelfthW1nHPlan_word : planWord twGtwelfthW1nHPlan = twGtwelfthW1nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem twGtwelfthW1nHPlan_ok : planOk twGtwelfthW1nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `twGtwelfthW1nG`. -/
def twGtwelfthW1nGPlan : List TPlan :=
  [.letter (.qel (qmElt (4661015, true))),
    .letter (.sign 1889 0),
    .run
      [(0, true), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, false), (1, false), (0, false), (0, false),
        (1, false), (0, false), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (0, false), (0, false), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, true), (1, false), (0, true)]
      [.trans 4 8, .trans 4 0, .trans 0 2, .trans 8 6, .trans 9 3, .trans 8 1, .trans 10 9,
        .trans 8 7, .trans 0 4, .trans 6 8, .trans 1 8, .trans 8 6, .trans 8 10,
        .trans 10 7, .trans 6 3, .trans 7 10, .trans 3 4, .trans 8 4, .trans 10 9,
        .trans 9 2, .trans 4 3, .trans 5 3, .trans 4 8, .trans 8 0, .trans 3 2,
        .trans 7 2, .trans 10 0, .trans 1 2],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true)]
      [.trans 3 11, .trans 7 6, .trans 4 5, .trans 11 2, .trans 10 3, .trans 4 1, .trans 1 8,
        .trans 9 7, .trans 6 10, .trans 10 9, .trans 3 7, .trans 6 2, .trans 10 11,
        .trans 7 4, .trans 11 4, .trans 10 8, .trans 5 1, .trans 1 9, .trans 4 2,
        .trans 2 3, .trans 9 11, .trans 8 0, .trans 2 0, .trans 5 6, .trans 7 9,
        .trans 9 8, .trans 8 3, .trans 8 11, .trans 8 10, .trans 8 7, .trans 0 5,
        .trans 1 0, .trans 1 5, .trans 3 4, .trans 4 2, .trans 4 7, .trans 4 9,
        .trans 5 6, .trans 5 11, .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 3,
        .trans 6 4, .trans 6 7, .trans 6 9, .trans 9 10, .trans 11 2, .trans 11 4,
        .trans 11 7, .trans 11 9, .trans 11 10]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem twGtwelfthW1nGPlan_word : planWord twGtwelfthW1nGPlan = twGtwelfthW1nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem twGtwelfthW1nGPlan_ok : planOk twGtwelfthW1nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def twGtwelfthW1nHX : List SVec := tensorPlanF 64 twGtwelfthW1nHPlan (twelfthSrcXW 64)

/-- The packed tensor of the target image. -/
def twGtwelfthW1nGX : List SVec := tensorPlanF 64 twGtwelfthW1nGPlan (twelfthSrcXW 64)

/-- The representation of the source image. -/
def twGtwelfthW1nL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet twGtwelfthW1nH, ShortData.ofList twGtwelfthW1nHT, (1 /
      128),
    tensorRat 64 twGtwelfthW1nHX ((tensorWordDenAll twGtwelfthW1nH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def twGtwelfthW1nW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet twGtwelfthW1nG, ShortData.ofList twGtwelfthW1nGT, (1 /
      128),
    tensorRat 64 twGtwelfthW1nGX ((tensorWordDenAll twGtwelfthW1nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem twGtwelfthW1nH_check : twGtwelfthW1nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem twGtwelfthW1nD_ok : twGtwelfthW1nHD.ok = true ∧ twGtwelfthW1nGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem twGtwelfthW1nHD_cols : ∀ i : Fin 24, qmWordP (twGtwelfthW1nHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 twGtwelfthW1nHD.colsP i.val, twGtwelfthW1nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem twGtwelfthW1nHD_rows : ∀ i : Fin 24,
    fld 24 twGtwelfthW1nHD.rowsP i.val = rowsOf (fun j => fld 24 twGtwelfthW1nHD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem twGtwelfthW1nHT_check0 :
    shortCheckPk twGtwelfthW1nHD 10 15 ((twelfthShS.flat).take 15360) ((twGtwelfthW1nHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem twGtwelfthW1nHT_check1 :
    shortCheckPk twGtwelfthW1nHD 10 15 (((twelfthShS.flat).drop 15360).take 15360)
        (((twGtwelfthW1nHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem twGtwelfthW1nHT_check2 :
    shortCheckPk twGtwelfthW1nHD 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360)
        ((((twGtwelfthW1nHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem twGtwelfthW1nHT_check3 :
    shortCheckPk twGtwelfthW1nHD 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360)
        ((((twGtwelfthW1nHT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem twGtwelfthW1nHT_check : shortCheckF twGtwelfthW1nHD twelfthShS.flat twGtwelfthW1nHT = true
    :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW1nHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW1nHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW1nHT_check2)
    (shortCheckPk_sound _ 10 1 _ _ twGtwelfthW1nHT_check3)))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem twGtwelfthW1nT_labels : twGtwelfthW1nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    twGtwelfthW1nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem twGtwelfthW1nH_growth : tensorWordGrowthAll twGtwelfthW1nH * 15 = 983040 := by decide

/-- The word bound of the target word. -/
theorem twGtwelfthW1nG_growth : tensorWordGrowthAll twGtwelfthW1nG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem twGtwelfthW1nL_actual : griessConwayEncode (rhoLocal (identWordLocal twGtwelfthW1nH)
    (generatedAxisGlobalTwelveRepresentative 10)) = twGtwelfthW1nL.real := by
  have hT := (tensorPlanF_actual twGtwelfthW1nHPlan twGtwelfthW1nHPlan_ok (twelfthSrcXW_bnd (w :=
      64) (by norm_num))
    (by rw [twGtwelfthW1nHPlan_word, twGtwelfthW1nH_growth]; norm_num) 32).2
  rw [twGtwelfthW1nHPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) twGtwelfthW1nHW twGtwelfthW1nH_check
      twGtwelfthW1nHD twGtwelfthW1nD_ok.1 twGtwelfthW1nHD_cols
    twGtwelfthW1nHD_rows twGtwelfthW1nHT twGtwelfthW1nHT_check _ hT _ (twelfthSrcS_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
