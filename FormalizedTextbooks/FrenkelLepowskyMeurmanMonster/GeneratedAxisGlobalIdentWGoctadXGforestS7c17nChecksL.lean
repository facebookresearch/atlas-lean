/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c17nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Seventh[26]- <-> Tenth[66]+
(record gforest:S7c17-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadXGforestS7c17nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadXGforestS7c17nH : List IdentLetter := wGoctadXGforestS7c17nHW.map Prod.fst

/-- The target word. -/
def wGoctadXGforestS7c17nG : List IdentLetter := wGoctadXGforestS7c17nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadXGforestS7c17nH`. -/
def wGoctadXGforestS7c17nHPlan : List TPlan :=
  [.letter (.xi),
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
        .trans 11 7, .trans 11 9, .trans 11 10],
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
theorem wGoctadXGforestS7c17nHPlan_word : planWord wGoctadXGforestS7c17nHPlan =
    wGoctadXGforestS7c17nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadXGforestS7c17nHPlan_ok : planOk wGoctadXGforestS7c17nHPlan = true := by
    decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadXGforestS7c17nG`. -/
def wGoctadXGforestS7c17nGPlan : List TPlan :=
  [.letter (.qel (qmElt (3146392, true))),
    .letter (.sign 1488 0),
    .run
      [(0, true), (0, true), (1, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, true), (0, true), (1, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, true), (1, false), (0, true), (1, false), (0, false),
        (0, false), (0, false), (1, false), (0, true), (0, true), (0, true), (1, true),
        (0, true), (1, true), (0, true), (0, true), (1, true), (0, true), (0, true),
        (0, true), (1, true), (0, true), (1, true), (0, false), (0, false), (1, true),
        (0, false), (0, false), (0, false), (1, true), (0, false), (1, true), (0, false),
        (0, false), (1, false), (0, true), (1, false), (0, false), (1, false), (0, true),
        (0, true), (1, false), (0, false), (1, false), (0, true), (1, false), (0, false),
        (1, false), (0, false), (1, false), (0, true), (1, false), (0, false), (1, false)]
      [.trans 7 5, .trans 0 3, .trans 2 0, .trans 1 2, .trans 3 0, .trans 9 7, .trans 7 4,
        .trans 4 6, .trans 8 4, .trans 6 5, .trans 4 5, .trans 0 2, .trans 5 7,
        .trans 2 1],
    .letter (.xi),
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadXGforestS7c17nGPlan_word : planWord wGoctadXGforestS7c17nGPlan =
    wGoctadXGforestS7c17nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadXGforestS7c17nGPlan_ok : planOk wGoctadXGforestS7c17nGPlan = true := by
    decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadXGforestS7c17nHX : List SVec := tensorPlanF 64 wGoctadXGforestS7c17nHPlan
    (srcSeventhX0F 64)

/-- The packed tensor of the target image. -/
def wGoctadXGforestS7c17nGX : List SVec := tensorPlanF 64 wGoctadXGforestS7c17nGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGoctadXGforestS7c17nL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet wGoctadXGforestS7c17nH, ShortData.ofList
      wGoctadXGforestS7c17nHT, (1 / 32),
    tensorRat 64 wGoctadXGforestS7c17nHX ((tensorWordDenAll wGoctadXGforestS7c17nH : ℚ) *
        srcSeventhD0)⟩

/-- The representation of the target image. -/
def wGoctadXGforestS7c17nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGoctadXGforestS7c17nG, ShortData.ofList
      wGoctadXGforestS7c17nGT, (1 / 128),
    tensorRat 64 wGoctadXGforestS7c17nGX ((tensorWordDenAll wGoctadXGforestS7c17nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadXGforestS7c17nH_check : wGoctadXGforestS7c17nHW.all (fun p => identLetterCheckP p.1
    p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadXGforestS7c17nD_ok : wGoctadXGforestS7c17nHD.ok = true ∧ wGoctadXGforestS7c17nGD.ok
    = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadXGforestS7c17nHD_cols : ∀ i : Fin 24, qmWordP (wGoctadXGforestS7c17nHW.map
    Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGoctadXGforestS7c17nHD.colsP i.val, wGoctadXGforestS7c17nHD.coeff.testBit i.val) :=
        by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadXGforestS7c17nHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadXGforestS7c17nHD.rowsP i.val = rowsOf (fun j => fld 24
        wGoctadXGforestS7c17nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadXGforestS7c17nHT_check : shortCheckF wGoctadXGforestS7c17nHD seventhShS.flat
    wGoctadXGforestS7c17nHT = true :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadXGforestS7c17nT_labels : wGoctadXGforestS7c17nHT.all (fun p => decide (p.1 <
    98280)) = true ∧
    wGoctadXGforestS7c17nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadXGforestS7c17nH_growth : tensorWordGrowthAll wGoctadXGforestS7c17nH * (4 *
    (16777216 * 8) + 276 * 6144) = 9035649118109696 := by decide

/-- The word bound of the target word. -/
theorem wGoctadXGforestS7c17nG_growth : tensorWordGrowthAll wGoctadXGforestS7c17nG * 15 = 7864320
    := by decide

/-- The coordinates of the source image. -/
theorem wGoctadXGforestS7c17nL_actual : griessConwayEncode (rhoLocal (identWordLocal
    wGoctadXGforestS7c17nH)
    (generatedAxisGlobalTwelveRepresentative 6)) = wGoctadXGforestS7c17nL.real := by
  have hT := (tensorPlanF_actual wGoctadXGforestS7c17nHPlan wGoctadXGforestS7c17nHPlan_ok
      (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [wGoctadXGforestS7c17nHPlan_word, wGoctadXGforestS7c17nH_growth]; norm_num)
        srcSeventhD0).2
  rw [wGoctadXGforestS7c17nHPlan_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 64) wGoctadXGforestS7c17nHW
      wGoctadXGforestS7c17nH_check wGoctadXGforestS7c17nHD wGoctadXGforestS7c17nD_ok.1
      wGoctadXGforestS7c17nHD_cols
    wGoctadXGforestS7c17nHD_rows wGoctadXGforestS7c17nHT wGoctadXGforestS7c17nHT_check _ hT _
        (seventhSrcS_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
