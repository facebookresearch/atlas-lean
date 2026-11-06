/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c11nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Seventh[18]- <-> Tenth[68]-
(record gforest:S7c11-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadXGforestS7c11nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadXGforestS7c11nH : List IdentLetter := wGoctadXGforestS7c11nHW.map Prod.fst

/-- The target word. -/
def wGoctadXGforestS7c11nG : List IdentLetter := wGoctadXGforestS7c11nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadXGforestS7c11nH`. -/
def wGoctadXGforestS7c11nHPlan : List TPlan :=
  [.letter (.xi),
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
        .trans 8 2, .trans 8 4, .trans 8 11],
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadXGforestS7c11nHPlan_word : planWord wGoctadXGforestS7c11nHPlan =
    wGoctadXGforestS7c11nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadXGforestS7c11nHPlan_ok : planOk wGoctadXGforestS7c11nHPlan = true := by
    decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadXGforestS7c11nG`. -/
def wGoctadXGforestS7c11nGPlan : List TPlan :=
  [.letter (.qel (qmElt (12200389, true))),
    .letter (.sign 826 0),
    .run
      [(0, false), (1, false), (0, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, true), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (1, false), (0, true), (0, true), (0, true),
        (1, true), (0, false), (0, false), (1, true), (0, false), (1, true), (0, true),
        (1, true), (0, true), (1, true), (0, true), (0, true), (0, true), (1, true),
        (0, true), (1, true), (0, false), (1, true), (0, false), (0, false), (0, false),
        (0, false), (0, false), (1, false), (0, true), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, true), (1, false), (0, false), (1, false),
        (0, false), (0, false), (0, false), (1, false), (0, true), (0, true)]
      [.trans 5 1, .trans 10 7, .trans 3 5, .trans 7 0, .trans 0 9, .trans 1 3, .trans 6 2,
        .trans 2 3, .trans 2 10, .trans 8 0, .trans 6 11, .trans 3 8, .trans 5 8,
        .trans 8 1, .trans 9 6, .trans 9 4, .trans 1 7, .trans 2 6, .trans 7 6,
        .trans 6 5, .trans 5 0, .trans 1 11, .trans 5 10, .trans 10 7, .trans 7 2,
        .trans 0 9, .trans 2 8, .trans 2 11, .trans 3 2, .trans 3 8, .trans 3 11,
        .trans 4 0, .trans 4 2, .trans 4 3, .trans 4 8, .trans 4 9, .trans 4 11,
        .trans 6 8, .trans 6 9, .trans 9 0, .trans 9 2, .trans 9 3, .trans 9 4,
        .trans 9 6, .trans 9 11],
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadXGforestS7c11nGPlan_word : planWord wGoctadXGforestS7c11nGPlan =
    wGoctadXGforestS7c11nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadXGforestS7c11nGPlan_ok : planOk wGoctadXGforestS7c11nGPlan = true := by
    decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadXGforestS7c11nHX : List SVec := tensorPlanF 64 wGoctadXGforestS7c11nHPlan
    (srcSeventhX0F 64)

/-- The packed tensor of the target image. -/
def wGoctadXGforestS7c11nGX : List SVec := tensorPlanF 64 wGoctadXGforestS7c11nGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGoctadXGforestS7c11nL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet wGoctadXGforestS7c11nH, ShortData.ofList
      wGoctadXGforestS7c11nHT, (1 / 32),
    tensorRat 64 wGoctadXGforestS7c11nHX ((tensorWordDenAll wGoctadXGforestS7c11nH : ℚ) *
        srcSeventhD0)⟩

/-- The representation of the target image. -/
def wGoctadXGforestS7c11nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGoctadXGforestS7c11nG, ShortData.ofList
      wGoctadXGforestS7c11nGT, (1 / 128),
    tensorRat 64 wGoctadXGforestS7c11nGX ((tensorWordDenAll wGoctadXGforestS7c11nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadXGforestS7c11nH_check : wGoctadXGforestS7c11nHW.all (fun p => identLetterCheckP p.1
    p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadXGforestS7c11nD_ok : wGoctadXGforestS7c11nHD.ok = true ∧ wGoctadXGforestS7c11nGD.ok
    = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadXGforestS7c11nHD_cols : ∀ i : Fin 24, qmWordP (wGoctadXGforestS7c11nHW.map
    Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGoctadXGforestS7c11nHD.colsP i.val, wGoctadXGforestS7c11nHD.coeff.testBit i.val) :=
        by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadXGforestS7c11nHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadXGforestS7c11nHD.rowsP i.val = rowsOf (fun j => fld 24
        wGoctadXGforestS7c11nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadXGforestS7c11nHT_check : shortCheckF wGoctadXGforestS7c11nHD seventhShS.flat
    wGoctadXGforestS7c11nHT = true :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadXGforestS7c11nT_labels : wGoctadXGforestS7c11nHT.all (fun p => decide (p.1 <
    98280)) = true ∧
    wGoctadXGforestS7c11nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadXGforestS7c11nH_growth : tensorWordGrowthAll wGoctadXGforestS7c11nH * (4 *
    (16777216 * 8) + 276 * 6144) = 9035649118109696 := by decide

/-- The word bound of the target word. -/
theorem wGoctadXGforestS7c11nG_growth : tensorWordGrowthAll wGoctadXGforestS7c11nG * 15 = 7864320
    := by decide

/-- The coordinates of the source image. -/
theorem wGoctadXGforestS7c11nL_actual : griessConwayEncode (rhoLocal (identWordLocal
    wGoctadXGforestS7c11nH)
    (generatedAxisGlobalTwelveRepresentative 6)) = wGoctadXGforestS7c11nL.real := by
  have hT := (tensorPlanF_actual wGoctadXGforestS7c11nHPlan wGoctadXGforestS7c11nHPlan_ok
      (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [wGoctadXGforestS7c11nHPlan_word, wGoctadXGforestS7c11nH_growth]; norm_num)
        srcSeventhD0).2
  rw [wGoctadXGforestS7c11nHPlan_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 64) wGoctadXGforestS7c11nHW
      wGoctadXGforestS7c11nH_check wGoctadXGforestS7c11nHD wGoctadXGforestS7c11nD_ok.1
      wGoctadXGforestS7c11nHD_cols
    wGoctadXGforestS7c11nHD_rows wGoctadXGforestS7c11nHT wGoctadXGforestS7c11nHT_check _ hT _
        (seventhSrcS_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
