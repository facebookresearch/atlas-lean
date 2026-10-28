/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Twelfth[30]- <->
Twelfth[30]+ (record gtwelfth:W30+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGtwelfthW30pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGtwelfthW30pH : List IdentLetter := wGtwelfthW30pHW.map Prod.fst

/-- The target word. -/
def wGtwelfthW30pG : List IdentLetter := wGtwelfthW30pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGtwelfthW30pH`. -/
def wGtwelfthW30pHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, true), (0, true), (1, true), (0, false), (0, false)]
      [.trans 5 1, .trans 5 8, .trans 3 10, .trans 7 6, .trans 2 3, .trans 4 10, .trans 0 5,
        .trans 10 5, .trans 10 6, .trans 6 9, .trans 0 9, .trans 9 0, .trans 0 6,
        .trans 9 2, .trans 10 4, .trans 4 7, .trans 2 5, .trans 1 5, .trans 8 0,
        .trans 0 8, .trans 2 7, .trans 7 2, .trans 5 4, .trans 4 10, .trans 10 1,
        .trans 1 2, .trans 2 3, .trans 0 7, .trans 6 0, .trans 6 7, .trans 7 0,
        .trans 7 4, .trans 7 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGtwelfthW30pHPlan_word : planWord wGtwelfthW30pHPlan = wGtwelfthW30pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGtwelfthW30pHPlan_ok : planOk wGtwelfthW30pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGtwelfthW30pG`. -/
def wGtwelfthW30pGPlan : List TPlan :=
  [.letter (.qel (qmElt (1393900, true))),
    .letter (.sign 1188 0),
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, true), (0, true), (1, true), (0, false), (0, false)]
      [.trans 5 1, .trans 5 8, .trans 3 10, .trans 7 6, .trans 2 3, .trans 4 10, .trans 0 5,
        .trans 10 5, .trans 10 6, .trans 6 9, .trans 0 9, .trans 9 0, .trans 0 6,
        .trans 9 2, .trans 10 4, .trans 4 7, .trans 2 5, .trans 1 5, .trans 8 0,
        .trans 0 8, .trans 2 7, .trans 7 2, .trans 5 4, .trans 4 10, .trans 10 1,
        .trans 1 2, .trans 2 3, .trans 0 7, .trans 6 0, .trans 6 7, .trans 7 0,
        .trans 7 4, .trans 7 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGtwelfthW30pGPlan_word : planWord wGtwelfthW30pGPlan = wGtwelfthW30pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGtwelfthW30pGPlan_ok : planOk wGtwelfthW30pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGtwelfthW30pHX : List SVec := tensorPlanF 64 wGtwelfthW30pHPlan (twelfthSrcXW 64)

/-- The packed tensor of the target image. -/
def wGtwelfthW30pGX : List SVec := tensorPlanF 64 wGtwelfthW30pGPlan (twelfthSrcXW 64)

/-- The representation of the source image. -/
def wGtwelfthW30pL : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet wGtwelfthW30pH, ShortData.ofList wGtwelfthW30pHT, (1 /
      128),
    tensorRat 64 wGtwelfthW30pHX ((tensorWordDenAll wGtwelfthW30pH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGtwelfthW30pW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet wGtwelfthW30pG, ShortData.ofList wGtwelfthW30pGT, (1 /
      128),
    tensorRat 64 wGtwelfthW30pGX ((tensorWordDenAll wGtwelfthW30pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGtwelfthW30pH_check : wGtwelfthW30pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGtwelfthW30pD_ok : wGtwelfthW30pHD.ok = true ∧ wGtwelfthW30pGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGtwelfthW30pHD_cols : ∀ i : Fin 24, qmWordP (wGtwelfthW30pHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGtwelfthW30pHD.colsP i.val, wGtwelfthW30pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGtwelfthW30pHD_rows : ∀ i : Fin 24,
    fld 24 wGtwelfthW30pHD.rowsP i.val = rowsOf (fun j => fld 24 wGtwelfthW30pHD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGtwelfthW30pHT_check : shortCheckF wGtwelfthW30pHD twelfthShS.flat wGtwelfthW30pHT = true
    :=
  shortCheckPk_sound _ 10 46 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGtwelfthW30pT_labels : wGtwelfthW30pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGtwelfthW30pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGtwelfthW30pH_growth : tensorWordGrowthAll wGtwelfthW30pH * 15 = 983040 := by decide

/-- The word bound of the target word. -/
theorem wGtwelfthW30pG_growth : tensorWordGrowthAll wGtwelfthW30pG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem wGtwelfthW30pL_actual : griessConwayEncode (rhoLocal (identWordLocal wGtwelfthW30pH)
    (generatedAxisGlobalTwelveRepresentative 10)) = wGtwelfthW30pL.real := by
  have hT := (tensorPlanF_actual wGtwelfthW30pHPlan wGtwelfthW30pHPlan_ok (twelfthSrcXW_bnd (w :=
      64) (by norm_num))
    (by rw [wGtwelfthW30pHPlan_word, wGtwelfthW30pH_growth]; norm_num) 32).2
  rw [wGtwelfthW30pHPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) wGtwelfthW30pHW wGtwelfthW30pH_check
      wGtwelfthW30pHD wGtwelfthW30pD_ok.1 wGtwelfthW30pHD_cols
    wGtwelfthW30pHD_rows wGtwelfthW30pHT wGtwelfthW30pHT_check _ hT _ (twelfthSrcS_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
