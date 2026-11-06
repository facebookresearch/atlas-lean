/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Twelfth[13]- <->
Twelfth[13]+ (record gtwelfth:W13+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def twGtwelfthW13pH : List IdentLetter := twGtwelfthW13pHW.map Prod.fst

/-- The target word. -/
def twGtwelfthW13pG : List IdentLetter := twGtwelfthW13pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `twGtwelfthW13pH`. -/
def twGtwelfthW13pHPlan : List TPlan :=
  [.letter (.xi),
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
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem twGtwelfthW13pHPlan_word : planWord twGtwelfthW13pHPlan = twGtwelfthW13pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem twGtwelfthW13pHPlan_ok : planOk twGtwelfthW13pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `twGtwelfthW13pG`. -/
def twGtwelfthW13pGPlan : List TPlan :=
  [.letter (.qel (qmElt (7541136, true))),
    .letter (.sign 1862 0),
    .run
      [(0, true), (1, false), (0, true), (0, true), (0, true), (1, false), (0, false),
        (0, false), (0, false), (1, false), (0, true), (0, true), (1, false), (0, true),
        (1, false), (0, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, true), (0, true), (0, true),
        (1, false)]
      [.trans 6 9, .trans 2 1, .trans 2 6, .trans 0 3, .trans 5 4, .trans 7 10, .trans 1 11,
        .trans 2 8, .trans 8 5, .trans 9 0, .trans 10 6, .trans 5 0, .trans 0 2,
        .trans 2 11, .trans 10 3, .trans 3 7, .trans 10 8, .trans 10 9, .trans 9 7,
        .trans 7 9, .trans 7 4, .trans 4 3, .trans 7 5, .trans 4 8, .trans 0 8,
        .trans 1 0, .trans 1 8, .trans 2 3, .trans 2 9, .trans 3 0, .trans 3 1,
        .trans 3 6, .trans 3 8, .trans 5 7, .trans 6 5, .trans 6 7, .trans 7 5,
        .trans 7 6, .trans 8 10, .trans 9 0, .trans 9 8, .trans 9 10, .trans 10 0,
        .trans 10 1, .trans 10 2, .trans 10 3, .trans 10 8, .trans 10 9],
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
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem twGtwelfthW13pGPlan_word : planWord twGtwelfthW13pGPlan = twGtwelfthW13pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem twGtwelfthW13pGPlan_ok : planOk twGtwelfthW13pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def twGtwelfthW13pHX : List SVec := tensorPlanF 80 twGtwelfthW13pHPlan (twelfthSrcXW 80)

/-- The packed tensor of the target image. -/
def twGtwelfthW13pGX : List SVec := tensorPlanF 80 twGtwelfthW13pGPlan (twelfthSrcXW 80)

/-- The representation of the source image. -/
def twGtwelfthW13pL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet twGtwelfthW13pH, ShortData.ofList twGtwelfthW13pHT, (1 /
      128),
    tensorRat 80 twGtwelfthW13pHX ((tensorWordDenAll twGtwelfthW13pH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def twGtwelfthW13pW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet twGtwelfthW13pG, ShortData.ofList twGtwelfthW13pGT, (1 /
      128),
    tensorRat 80 twGtwelfthW13pGX ((tensorWordDenAll twGtwelfthW13pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem twGtwelfthW13pH_check : twGtwelfthW13pHW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem twGtwelfthW13pD_ok : twGtwelfthW13pHD.ok = true ∧ twGtwelfthW13pGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem twGtwelfthW13pHD_cols : ∀ i : Fin 24, qmWordP (twGtwelfthW13pHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 twGtwelfthW13pHD.colsP i.val, twGtwelfthW13pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem twGtwelfthW13pHD_rows : ∀ i : Fin 24,
    fld 24 twGtwelfthW13pHD.rowsP i.val = rowsOf (fun j => fld 24 twGtwelfthW13pHD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem twGtwelfthW13pHT_check0 :
    shortCheckPk twGtwelfthW13pHD 10 15 ((twelfthShS.flat).take 15360) ((twGtwelfthW13pHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem twGtwelfthW13pHT_check1 :
    shortCheckPk twGtwelfthW13pHD 10 15 (((twelfthShS.flat).drop 15360).take 15360)
        (((twGtwelfthW13pHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem twGtwelfthW13pHT_check2 :
    shortCheckPk twGtwelfthW13pHD 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360)
        ((((twGtwelfthW13pHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem twGtwelfthW13pHT_check3 :
    shortCheckPk twGtwelfthW13pHD 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360)
        ((((twGtwelfthW13pHT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem twGtwelfthW13pHT_check : shortCheckF twGtwelfthW13pHD twelfthShS.flat twGtwelfthW13pHT =
    true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW13pHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW13pHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW13pHT_check2)
    (shortCheckPk_sound _ 10 1 _ _ twGtwelfthW13pHT_check3)))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem twGtwelfthW13pT_labels : twGtwelfthW13pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    twGtwelfthW13pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem twGtwelfthW13pH_growth : tensorWordGrowthAll twGtwelfthW13pH * 15 = 251658240 := by decide

/-- The word bound of the target word. -/
theorem twGtwelfthW13pG_growth : tensorWordGrowthAll twGtwelfthW13pG * 15 = 2013265920 := by decide

/-- The coordinates of the source image. -/
theorem twGtwelfthW13pL_actual : griessConwayEncode (rhoLocal (identWordLocal twGtwelfthW13pH)
    (generatedAxisGlobalTwelveRepresentative 10)) = twGtwelfthW13pL.real := by
  have hT := (tensorPlanF_actual twGtwelfthW13pHPlan twGtwelfthW13pHPlan_ok (twelfthSrcXW_bnd (w
      := 80) (by norm_num))
    (by rw [twGtwelfthW13pHPlan_word, twGtwelfthW13pH_growth]; norm_num) 32).2
  rw [twGtwelfthW13pHPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 80) twGtwelfthW13pHW twGtwelfthW13pH_check
      twGtwelfthW13pHD twGtwelfthW13pD_ok.1 twGtwelfthW13pHD_cols
    twGtwelfthW13pHD_rows twGtwelfthW13pHT twGtwelfthW13pHT_check _ hT _ (twelfthSrcS_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
