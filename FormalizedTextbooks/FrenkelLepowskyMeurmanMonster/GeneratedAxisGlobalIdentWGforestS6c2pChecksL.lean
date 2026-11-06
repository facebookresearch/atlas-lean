/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c2pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Fourth[18]- <-> Sixth[3]+
(record gforest:S6c2+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGforestS6c2pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGforestS6c2pH : List IdentLetter := wGforestS6c2pHW.map Prod.fst

/-- The target word. -/
def wGforestS6c2pG : List IdentLetter := wGforestS6c2pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGforestS6c2pH`. -/
def wGforestS6c2pHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGforestS6c2pHPlan_word : planWord wGforestS6c2pHPlan = wGforestS6c2pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGforestS6c2pHPlan_ok : planOk wGforestS6c2pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGforestS6c2pG`. -/
def wGforestS6c2pGPlan : List TPlan :=
  [.letter (.qel (qmElt (4076736, true))),
    .letter (.sign 3 0),
    .run
      [(0, false), (1, false), (0, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, true), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (1, false), (0, true), (0, true), (0, true),
        (1, true), (0, false), (0, false), (1, true), (0, false), (1, true), (0, true),
        (1, true), (0, true), (1, true), (0, true), (0, true), (0, true), (1, true),
        (0, true), (1, true), (0, false), (1, true), (0, false), (0, false), (0, false),
        (1, false), (0, false), (0, false), (1, false), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, true), (0, true), (0, true), (1, false), (0, true),
        (0, true), (1, false)]
      [.trans 2 3, .trans 0 1, .trans 0 2, .trans 3 2, .trans 7 5, .trans 4 6, .trans 6 4,
        .trans 10 0, .trans 4 6, .trans 8 1, .trans 7 2, .trans 9 2, .trans 2 3,
        .trans 4 1, .trans 4 2, .trans 8 3, .trans 6 0, .trans 10 5, .trans 5 7,
        .trans 7 5],
    .letter (.xi),
    .run
      [(1, false)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, false)]
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
theorem wGforestS6c2pGPlan_word : planWord wGforestS6c2pGPlan = wGforestS6c2pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGforestS6c2pGPlan_ok : planOk wGforestS6c2pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGforestS6c2pHX : List SVec := tensorPlanF 64 wGforestS6c2pHPlan (sixthSXF 64)

/-- The packed tensor of the target image. -/
def wGforestS6c2pGX : List SVec := tensorPlanF 64 wGforestS6c2pGPlan (fourthSrcXW 64)

/-- The representation of the source image. -/
def wGforestS6c2pL : IdentVec :=
  ⟨sixthSrcMat.act identSpatialAlphabet wGforestS6c2pH, ShortData.ofList wGforestS6c2pHT, 1 / 32,
    tensorRat 64 wGforestS6c2pHX ((tensorWordDenAll wGforestS6c2pH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGforestS6c2pW : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet wGforestS6c2pG, ShortData.ofList wGforestS6c2pGT, 1 / 8,
    tensorRat 64 wGforestS6c2pGX ((tensorWordDenAll wGforestS6c2pG : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGforestS6c2pH_check : wGforestS6c2pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGforestS6c2pD_ok : wGforestS6c2pHD.ok = true ∧ wGforestS6c2pGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGforestS6c2pHD_cols : ∀ i : Fin 24, qmWordP (wGforestS6c2pHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS6c2pHD.colsP i.val, wGforestS6c2pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGforestS6c2pHD_rows : ∀ i : Fin 24,
    fld 24 wGforestS6c2pHD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS6c2pHD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGforestS6c2pHT_check : shortCheckF wGforestS6c2pHD sixthLitShort.flat wGforestS6c2pHT =
    true :=
  shortCheckPk_sound _ 10 30 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGforestS6c2pT_labels : wGforestS6c2pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGforestS6c2pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGforestS6c2pH_growth : tensorWordGrowthAll wGforestS6c2pH * (2 ^ 8 - 1) = 16711680 := by
    decide

/-- The word bound of the target word. -/
theorem wGforestS6c2pG_growth : tensorWordGrowthAll wGforestS6c2pG * 56 = 7516192768 := by decide

/-- The coordinates of the source image. -/
theorem wGforestS6c2pL_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS6c2pH)
    (generatedAxisGlobalTwelveRepresentative 5)) = wGforestS6c2pL.real := by
  have hT := (tensorPlanF_actual wGforestS6c2pHPlan wGforestS6c2pHPlan_ok (sixthSXF_bndF (w := 64)
      (by norm_num))
    (by rw [wGforestS6c2pHPlan_word, wGforestS6c2pH_growth]; norm_num) 32).2
  rw [wGforestS6c2pHPlan_word] at hT
  exact IdentVec.word_actual (sixthSrcVecF 64) wGforestS6c2pHW wGforestS6c2pH_check
      wGforestS6c2pHD wGforestS6c2pD_ok.1 wGforestS6c2pHD_cols
    wGforestS6c2pHD_rows wGforestS6c2pHT wGforestS6c2pHT_check _ hT _ (sixthSrcF_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
