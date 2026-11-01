/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[10]- <-> Seventh[19]+
(record gforest:S7c12+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGforestS7c12pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGforestS7c12pH : List IdentLetter := wGforestS7c12pHW.map Prod.fst

/-- The target word. -/
def wGforestS7c12pG : List IdentLetter := wGforestS7c12pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGforestS7c12pH`. -/
def wGforestS7c12pHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGforestS7c12pHPlan_word : planWord wGforestS7c12pHPlan = wGforestS7c12pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGforestS7c12pHPlan_ok : planOk wGforestS7c12pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGforestS7c12pG`. -/
def wGforestS7c12pGPlan : List TPlan :=
  [.letter (.qel (qmElt (6868301, true))),
    .letter (.sign 1944 0),
    .run
      [(1, false), (0, true), (1, false), (0, false), (0, false), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
        (0, false), (0, false), (1, false), (0, false), (1, false), (0, true), (0, true),
        (1, true), (0, true), (1, true), (0, false), (0, false), (1, true), (0, false),
        (0, false), (1, true), (0, false), (0, false), (0, false), (1, true), (0, false),
        (1, true), (0, false), (0, false), (1, true), (0, false), (1, true), (0, true),
        (1, true), (0, true), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, true), (0, true), (0, true), (1, false), (0, false),
        (0, false), (1, false), (0, false), (0, false)]
      [.trans 1 0, .trans 0 1, .trans 0 2, .trans 0 3, .trans 0 8, .trans 3 1, .trans 1 3,
        .trans 5 2, .trans 2 0, .trans 2 1, .trans 2 5, .trans 2 6, .trans 2 7,
        .trans 8 3, .trans 3 0, .trans 3 2, .trans 3 8, .trans 4 1, .trans 4 2,
        .trans 4 3, .trans 4 6, .trans 4 8, .trans 5 2, .trans 5 9, .trans 5 10,
        .trans 8 6, .trans 6 2, .trans 6 4, .trans 6 8, .trans 7 1, .trans 7 2,
        .trans 7 3, .trans 7 5, .trans 7 6, .trans 7 8, .trans 9 8, .trans 8 3,
        .trans 8 6, .trans 8 7, .trans 8 9, .trans 8 10, .trans 10 9, .trans 9 0,
        .trans 9 2, .trans 9 4, .trans 9 5, .trans 9 10, .trans 10 0, .trans 10 3,
        .trans 10 6, .trans 10 8, .trans 10 9],
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
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGforestS7c12pGPlan_word : planWord wGforestS7c12pGPlan = wGforestS7c12pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGforestS7c12pGPlan_ok : planOk wGforestS7c12pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGforestS7c12pHX : List SVec := tensorPlanF 64 wGforestS7c12pHPlan (srcSeventhX0F 64)

/-- The packed tensor of the target image. -/
def wGforestS7c12pGX : List SVec := tensorPlanF 64 wGforestS7c12pGPlan (rootEightSrcXL 64)

/-- The representation of the source image. -/
def wGforestS7c12pL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet wGforestS7c12pH, ShortData.ofList wGforestS7c12pHT, (1 /
      32),
    tensorRat 64 wGforestS7c12pHX ((tensorWordDenAll wGforestS7c12pH : ℚ) * srcSeventhD0)⟩

/-- The representation of the target image. -/
def wGforestS7c12pW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wGforestS7c12pG, ShortData.ofList wGforestS7c12pGT, (1
      / 128),
    tensorRat 64 wGforestS7c12pGX ((tensorWordDenAll wGforestS7c12pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGforestS7c12pH_check : wGforestS7c12pHW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGforestS7c12pD_ok : wGforestS7c12pHD.ok = true ∧ wGforestS7c12pGD.ok = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGforestS7c12pHD_cols : ∀ i : Fin 24, qmWordP (wGforestS7c12pHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS7c12pHD.colsP i.val, wGforestS7c12pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGforestS7c12pHD_rows : ∀ i : Fin 24,
    fld 24 wGforestS7c12pHD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS7c12pHD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGforestS7c12pHT_check : shortCheckF wGforestS7c12pHD seventhShS.flat wGforestS7c12pHT =
    true :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGforestS7c12pT_labels : wGforestS7c12pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wGforestS7c12pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGforestS7c12pH_growth : tensorWordGrowthAll wGforestS7c12pH * (4 * (16777216 * 8) + 276 *
    6144) = 9035649118109696 := by decide

/-- The word bound of the target word. -/
theorem wGforestS7c12pG_growth : tensorWordGrowthAll wGforestS7c12pG * 15 = 2013265920 := by decide

/-- The coordinates of the source image. -/
theorem wGforestS7c12pL_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS7c12pH)
    (generatedAxisGlobalTwelveRepresentative 6)) = wGforestS7c12pL.real := by
  have hT := (tensorPlanF_actual wGforestS7c12pHPlan wGforestS7c12pHPlan_ok (srcSeventhX0F_bnd (w
      := 64) (by norm_num))
    (by rw [wGforestS7c12pHPlan_word, wGforestS7c12pH_growth]; norm_num) srcSeventhD0).2
  rw [wGforestS7c12pHPlan_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 64) wGforestS7c12pHW wGforestS7c12pH_check
      wGforestS7c12pHD wGforestS7c12pD_ok.1 wGforestS7c12pHD_cols
    wGforestS7c12pHD_rows wGforestS7c12pHT wGforestS7c12pHT_check _ hT _ (seventhSrcS_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
