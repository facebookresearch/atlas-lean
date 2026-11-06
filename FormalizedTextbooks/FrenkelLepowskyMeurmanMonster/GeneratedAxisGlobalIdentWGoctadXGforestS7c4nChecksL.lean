/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c4nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Seventh[9]- <-> Tenth[1]+
(record gforest:S7c4-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadXGforestS7c4nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadXGforestS7c4nH : List IdentLetter := wGoctadXGforestS7c4nHW.map Prod.fst

/-- The target word. -/
def wGoctadXGforestS7c4nG : List IdentLetter := wGoctadXGforestS7c4nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadXGforestS7c4nH`. -/
def wGoctadXGforestS7c4nHPlan : List TPlan :=
  [.letter (.xi),
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
    .letter (.xi),
    .run
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadXGforestS7c4nHPlan_word : planWord wGoctadXGforestS7c4nHPlan =
    wGoctadXGforestS7c4nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadXGforestS7c4nHPlan_ok : planOk wGoctadXGforestS7c4nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadXGforestS7c4nG`. -/
def wGoctadXGforestS7c4nGPlan : List TPlan :=
  [.letter (.qel (qmElt (7720232, true))),
    .letter (.sign 1903 0),
    .run
      [(1, false), (0, false), (1, false), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, true), (0, true), (0, true), (1, false), (0, true), (1, false),
        (0, true), (0, true), (1, false), (0, true), (0, true), (1, false), (0, false),
        (0, false), (0, false), (0, false), (0, false), (1, true), (0, true), (1, true),
        (0, false), (1, true), (0, false), (0, false), (1, true), (0, true), (0, true),
        (0, true), (1, true), (0, true), (1, true), (0, false), (0, false), (1, true),
        (0, false), (0, false), (0, false), (1, true), (0, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, true), (1, false),
        (0, false), (1, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, true), (1, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, true)]
      [.trans 9 7, .trans 0 10, .trans 3 2, .trans 3 4, .trans 8 0, .trans 3 6, .trans 1 9,
        .trans 10 1, .trans 1 5, .trans 7 4, .trans 5 8, .trans 10 3, .trans 0 3,
        .trans 3 1, .trans 4 3, .trans 3 9, .trans 3 6, .trans 3 7, .trans 4 8,
        .trans 8 5, .trans 6 5, .trans 2 10, .trans 3 0, .trans 5 8, .trans 5 7,
        .trans 7 9, .trans 9 6, .trans 6 8, .trans 8 0, .trans 8 10],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true), (0, false), (0, false)]
      [.trans 3 8, .trans 11 3, .trans 6 1, .trans 10 4, .trans 6 10, .trans 0 6, .trans 10 0,
        .trans 1 11, .trans 10 5, .trans 3 7, .trans 9 11, .trans 4 11, .trans 11 3,
        .trans 11 7, .trans 7 6, .trans 6 8, .trans 4 5, .trans 6 2, .trans 0 9,
        .trans 6 5, .trans 0 2, .trans 5 8, .trans 8 2, .trans 2 7, .trans 8 3,
        .trans 5 10, .trans 5 11, .trans 11 9, .trans 6 1, .trans 1 7, .trans 7 11,
        .trans 7 2, .trans 3 4, .trans 9 4, .trans 4 9, .trans 9 3, .trans 9 11,
        .trans 11 4]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadXGforestS7c4nGPlan_word : planWord wGoctadXGforestS7c4nGPlan =
    wGoctadXGforestS7c4nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadXGforestS7c4nGPlan_ok : planOk wGoctadXGforestS7c4nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadXGforestS7c4nHX : List SVec := tensorPlanF 64 wGoctadXGforestS7c4nHPlan (srcSeventhX0F
    64)

/-- The packed tensor of the target image. -/
def wGoctadXGforestS7c4nGX : List SVec := tensorPlanF 64 wGoctadXGforestS7c4nGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGoctadXGforestS7c4nL : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet wGoctadXGforestS7c4nH, ShortData.ofList
      wGoctadXGforestS7c4nHT, (1 / 32),
    tensorRat 64 wGoctadXGforestS7c4nHX ((tensorWordDenAll wGoctadXGforestS7c4nH : ℚ) *
        srcSeventhD0)⟩

/-- The representation of the target image. -/
def wGoctadXGforestS7c4nW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGoctadXGforestS7c4nG, ShortData.ofList
      wGoctadXGforestS7c4nGT, (1 / 128),
    tensorRat 64 wGoctadXGforestS7c4nGX ((tensorWordDenAll wGoctadXGforestS7c4nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadXGforestS7c4nH_check : wGoctadXGforestS7c4nHW.all (fun p => identLetterCheckP p.1
    p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadXGforestS7c4nD_ok : wGoctadXGforestS7c4nHD.ok = true ∧ wGoctadXGforestS7c4nGD.ok =
    true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadXGforestS7c4nHD_cols : ∀ i : Fin 24, qmWordP (wGoctadXGforestS7c4nHW.map Prod.snd)
    (2 ^ i.val, false) =
    (fld 24 wGoctadXGforestS7c4nHD.colsP i.val, wGoctadXGforestS7c4nHD.coeff.testBit i.val) := by
        decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadXGforestS7c4nHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadXGforestS7c4nHD.rowsP i.val = rowsOf (fun j => fld 24
        wGoctadXGforestS7c4nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadXGforestS7c4nHT_check : shortCheckF wGoctadXGforestS7c4nHD seventhShS.flat
    wGoctadXGforestS7c4nHT = true :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadXGforestS7c4nT_labels : wGoctadXGforestS7c4nHT.all (fun p => decide (p.1 < 98280))
    = true ∧
    wGoctadXGforestS7c4nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadXGforestS7c4nH_growth : tensorWordGrowthAll wGoctadXGforestS7c4nH * (4 * (16777216
    * 8) + 276 * 6144) = 9035649118109696 := by decide

/-- The word bound of the target word. -/
theorem wGoctadXGforestS7c4nG_growth : tensorWordGrowthAll wGoctadXGforestS7c4nG * 15 = 7864320 :=
    by decide

/-- The coordinates of the source image. -/
theorem wGoctadXGforestS7c4nL_actual : griessConwayEncode (rhoLocal (identWordLocal
    wGoctadXGforestS7c4nH)
    (generatedAxisGlobalTwelveRepresentative 6)) = wGoctadXGforestS7c4nL.real := by
  have hT := (tensorPlanF_actual wGoctadXGforestS7c4nHPlan wGoctadXGforestS7c4nHPlan_ok
      (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [wGoctadXGforestS7c4nHPlan_word, wGoctadXGforestS7c4nH_growth]; norm_num) srcSeventhD0).2
  rw [wGoctadXGforestS7c4nHPlan_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 64) wGoctadXGforestS7c4nHW
      wGoctadXGforestS7c4nH_check wGoctadXGforestS7c4nHD wGoctadXGforestS7c4nD_ok.1
      wGoctadXGforestS7c4nHD_cols
    wGoctadXGforestS7c4nHD_rows wGoctadXGforestS7c4nHT wGoctadXGforestS7c4nHT_check _ hT _
        (seventhSrcS_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
