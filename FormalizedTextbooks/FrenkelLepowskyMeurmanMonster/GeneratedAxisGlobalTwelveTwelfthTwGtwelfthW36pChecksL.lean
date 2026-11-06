/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Twelfth[36]+ <->
Twelfth[36]+ (record gtwelfth:W36+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def twGtwelfthW36pH : List IdentLetter := twGtwelfthW36pHW.map Prod.fst

/-- The target word. -/
def twGtwelfthW36pG : List IdentLetter := twGtwelfthW36pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `twGtwelfthW36pH`. -/
def twGtwelfthW36pHPlan : List TPlan :=
  [.letter (.xi),
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
theorem twGtwelfthW36pHPlan_word : planWord twGtwelfthW36pHPlan = twGtwelfthW36pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem twGtwelfthW36pHPlan_ok : planOk twGtwelfthW36pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `twGtwelfthW36pG`. -/
def twGtwelfthW36pGPlan : List TPlan :=
  [.letter (.qel (qmElt (15709496, true))),
    .letter (.sign 1336 0),
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
theorem twGtwelfthW36pGPlan_word : planWord twGtwelfthW36pGPlan = twGtwelfthW36pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem twGtwelfthW36pGPlan_ok : planOk twGtwelfthW36pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def twGtwelfthW36pHX : List SVec := tensorPlanF 64 twGtwelfthW36pHPlan (twelfthSrcXW 64)

/-- The packed tensor of the target image. -/
def twGtwelfthW36pGX : List SVec := tensorPlanF 64 twGtwelfthW36pGPlan (twelfthSrcXW 64)

/-- The representation of the source image. -/
def twGtwelfthW36pL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet twGtwelfthW36pH, ShortData.ofList twGtwelfthW36pHT, (1 /
      128),
    tensorRat 64 twGtwelfthW36pHX ((tensorWordDenAll twGtwelfthW36pH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def twGtwelfthW36pW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet twGtwelfthW36pG, ShortData.ofList twGtwelfthW36pGT, (1 /
      128),
    tensorRat 64 twGtwelfthW36pGX ((tensorWordDenAll twGtwelfthW36pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem twGtwelfthW36pH_check : twGtwelfthW36pHW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem twGtwelfthW36pD_ok : twGtwelfthW36pHD.ok = true ∧ twGtwelfthW36pGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem twGtwelfthW36pHD_cols : ∀ i : Fin 24, qmWordP (twGtwelfthW36pHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 twGtwelfthW36pHD.colsP i.val, twGtwelfthW36pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem twGtwelfthW36pHD_rows : ∀ i : Fin 24,
    fld 24 twGtwelfthW36pHD.rowsP i.val = rowsOf (fun j => fld 24 twGtwelfthW36pHD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 0). -/
theorem twGtwelfthW36pHT_check0 :
    shortCheckPk twGtwelfthW36pHD 10 15 ((twelfthShS.flat).take 15360) ((twGtwelfthW36pHT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 1). -/
theorem twGtwelfthW36pHT_check1 :
    shortCheckPk twGtwelfthW36pHD 10 15 (((twelfthShS.flat).drop 15360).take 15360)
        (((twGtwelfthW36pHT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 2). -/
theorem twGtwelfthW36pHT_check2 :
    shortCheckPk twGtwelfthW36pHD 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360)
        ((((twGtwelfthW36pHT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. (part 3). -/
theorem twGtwelfthW36pHT_check3 :
    shortCheckPk twGtwelfthW36pHD 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360)
        ((((twGtwelfthW36pHT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source image is transported onto the literal targets. -/
theorem twGtwelfthW36pHT_check : shortCheckF twGtwelfthW36pHD twelfthShS.flat twGtwelfthW36pHT =
    true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW36pHT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW36pHT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW36pHT_check2)
    (shortCheckPk_sound _ 10 1 _ _ twGtwelfthW36pHT_check3)))

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem twGtwelfthW36pT_labels : twGtwelfthW36pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    twGtwelfthW36pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem twGtwelfthW36pH_growth : tensorWordGrowthAll twGtwelfthW36pH * 15 = 983040 := by decide

/-- The word bound of the target word. -/
theorem twGtwelfthW36pG_growth : tensorWordGrowthAll twGtwelfthW36pG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem twGtwelfthW36pL_actual : griessConwayEncode (rhoLocal (identWordLocal twGtwelfthW36pH)
    (generatedAxisGlobalTwelveRepresentative 10)) = twGtwelfthW36pL.real := by
  have hT := (tensorPlanF_actual twGtwelfthW36pHPlan twGtwelfthW36pHPlan_ok (twelfthSrcXW_bnd (w
      := 64) (by norm_num))
    (by rw [twGtwelfthW36pHPlan_word, twGtwelfthW36pH_growth]; norm_num) 32).2
  rw [twGtwelfthW36pHPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) twGtwelfthW36pHW twGtwelfthW36pH_check
      twGtwelfthW36pHD twGtwelfthW36pD_ok.1 twGtwelfthW36pHD_cols
    twGtwelfthW36pHD_rows twGtwelfthW36pHT twGtwelfthW36pHT_check _ hT _ (twelfthSrcS_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
