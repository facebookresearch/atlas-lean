/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[12]- <-> Twelfth[34]-
(record r8f:R86-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR86nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR86nH : List IdentLetter := wR8fR86nHW.map Prod.fst

/-- The target word. -/
def wR8fR86nG : List IdentLetter := wR8fR86nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR86nH`. -/
def wR8fR86nHPlan : List TPlan :=
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
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR86nHPlan_word : planWord wR8fR86nHPlan = wR8fR86nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR86nHPlan_ok : planOk wR8fR86nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR86nG`. -/
def wR8fR86nGPlan : List TPlan :=
  [.letter (.qel (qmElt (10279572, false))),
    .letter (.sign 1857 0),
    .run
      [(0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, true), (0, true), (0, true), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, true), (1, false), (0, false), (1, false), (0, false),
        (1, false), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false),
        (0, false)]
      [.trans 4 3, .trans 0 4, .trans 1 2, .trans 10 9, .trans 3 2, .trans 5 11, .trans 8 10,
        .trans 5 1, .trans 6 0, .trans 9 7, .trans 7 4, .trans 1 0, .trans 10 8,
        .trans 9 2, .trans 8 0, .trans 0 3, .trans 3 11, .trans 9 6, .trans 6 1,
        .trans 2 5, .trans 0 9, .trans 9 0, .trans 8 7, .trans 6 7, .trans 0 10,
        .trans 2 4, .trans 7 8, .trans 7 10, .trans 10 11, .trans 10 4, .trans 4 8,
        .trans 8 9, .trans 9 1, .trans 8 5, .trans 4 6, .trans 1 5, .trans 5 8,
        .trans 8 1, .trans 8 5],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (0, false), (1, true), (0, false)]
      [.trans 6 4, .trans 9 11, .trans 2 9, .trans 5 6, .trans 4 0, .trans 2 3, .trans 3 5,
        .trans 5 7, .trans 6 1, .trans 8 3, .trans 9 4, .trans 4 6, .trans 10 8,
        .trans 8 11, .trans 6 1, .trans 1 9, .trans 6 5, .trans 5 3, .trans 3 8,
        .trans 8 10, .trans 0 1, .trans 5 4, .trans 6 2, .trans 5 9, .trans 7 2,
        .trans 8 2, .trans 2 4, .trans 4 8, .trans 4 7, .trans 7 0, .trans 0 10,
        .trans 0 7, .trans 2 3],
    .letter (.xi),
    .run
      [(1, true), (0, false)]
      [.trans 10 11, .trans 0 10, .trans 1 6, .trans 4 1, .trans 1 0, .trans 10 4, .trans 4 3,
        .trans 1 2, .trans 9 10, .trans 6 0, .trans 0 5, .trans 4 6, .trans 6 1,
        .trans 7 1, .trans 2 1, .trans 1 4, .trans 10 11, .trans 0 7, .trans 3 6,
        .trans 1 8, .trans 8 3, .trans 8 9, .trans 9 2, .trans 2 9, .trans 9 2,
        .trans 0 11, .trans 3 8, .trans 4 5, .trans 5 0, .trans 5 9, .trans 5 11,
        .trans 6 0, .trans 6 7, .trans 6 11, .trans 7 3, .trans 7 8, .trans 8 3,
        .trans 8 4, .trans 8 5, .trans 8 6, .trans 8 7, .trans 8 9]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR86nGPlan_word : planWord wR8fR86nGPlan = wR8fR86nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR86nGPlan_ok : planOk wR8fR86nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR86nHX : List SVec := tensorPlanF 96 wR8fR86nHPlan (rootEightSrcXL 96)

/-- The packed tensor of the target image. -/
def wR8fR86nGX : List SVec := tensorPlanF 96 wR8fR86nGPlan (twelfthSrcXW 96)

/-- The representation of the source image. -/
def wR8fR86nL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR86nH, ShortData.ofList wR8fR86nHT, (1 / 128),
    tensorRat 96 wR8fR86nHX ((tensorWordDenAll wR8fR86nH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR86nW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet wR8fR86nG, ShortData.ofList wR8fR86nGT, (1 / 128),
    tensorRat 96 wR8fR86nGX ((tensorWordDenAll wR8fR86nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR86nH_check : wR8fR86nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR86nD_ok : wR8fR86nHD.ok = true ∧ wR8fR86nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR86nHD_cols : ∀ i : Fin 24, qmWordP (wR8fR86nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR86nHD.colsP i.val, wR8fR86nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR86nHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR86nHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR86nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR86nHT_check : shortCheckF wR8fR86nHD srcRootEightCShort.flat wR8fR86nHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR86nT_labels : wR8fR86nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR86nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR86nH_growth : tensorWordGrowthAll wR8fR86nH * 15 = 64424509440 := by decide

/-- The word bound of the target word. -/
theorem wR8fR86nG_growth : tensorWordGrowthAll wR8fR86nG * 15 = 2013265920 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR86nL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR86nH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR86nL.real := by
  have hT := (tensorPlanF_actual wR8fR86nHPlan wR8fR86nHPlan_ok (rootEightSrcXL_bnd (w := 96) (by
      norm_num))
    (by rw [wR8fR86nHPlan_word, wR8fR86nH_growth]; norm_num) 32).2
  rw [wR8fR86nHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 96) wR8fR86nHW wR8fR86nH_check wR8fR86nHD
      wR8fR86nD_ok.1 wR8fR86nHD_cols
    wR8fR86nHD_rows wR8fR86nHT wR8fR86nHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
