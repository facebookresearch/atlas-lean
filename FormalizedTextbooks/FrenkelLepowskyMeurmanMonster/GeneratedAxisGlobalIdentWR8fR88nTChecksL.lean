/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR88nTData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[20]- <-> Tenth[69]+
(record r8f:R88-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR88nTChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR88nTH : List IdentLetter := wR8fR88nTHW.map Prod.fst

/-- The target word. -/
def wR8fR88nTG : List IdentLetter := wR8fR88nTGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR88nTH`. -/
def wR8fR88nTHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
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
theorem wR8fR88nTHPlan_word : planWord wR8fR88nTHPlan = wR8fR88nTH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR88nTHPlan_ok : planOk wR8fR88nTHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR88nTG`. -/
def wR8fR88nTGPlan : List TPlan :=
  [.letter (.qel (qmElt (4491783, false))),
    .letter (.sign 67 0),
    .run
      [(0, true), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (1, false), (0, true), (1, false),
        (0, false), (0, false), (1, true), (0, false), (1, true), (0, true), (1, true),
        (0, false), (0, false), (0, false), (1, true), (0, false), (0, false), (1, true),
        (0, false), (1, true), (0, false), (0, false), (0, false), (1, true), (0, true),
        (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, false), (1, false), (0, true),
        (1, false), (0, true), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, true)]
      [.trans 0 1, .trans 0 7, .trans 0 9, .trans 3 1, .trans 1 0, .trans 1 3, .trans 1 4,
        .trans 1 6, .trans 1 9, .trans 1 10, .trans 4 2, .trans 2 1, .trans 2 4,
        .trans 2 5, .trans 2 7, .trans 3 0, .trans 3 8, .trans 7 4, .trans 4 0,
        .trans 4 1, .trans 4 2, .trans 4 3, .trans 4 7, .trans 8 5, .trans 5 0,
        .trans 5 3, .trans 5 4, .trans 5 8, .trans 9 6, .trans 6 1, .trans 6 2,
        .trans 6 3, .trans 6 4, .trans 6 9, .trans 8 7, .trans 7 1, .trans 7 2,
        .trans 7 3, .trans 7 4, .trans 7 5, .trans 7 8, .trans 8 0, .trans 8 3,
        .trans 8 4, .trans 8 6, .trans 8 7, .trans 8 10, .trans 10 9, .trans 9 4,
        .trans 9 7, .trans 9 8, .trans 9 10, .trans 10 0, .trans 10 2, .trans 10 3,
        .trans 10 4, .trans 10 6, .trans 10 7],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (0, true), (0, true), (1, true), (0, false)]
      [.trans 6 1, .trans 3 8, .trans 6 2, .trans 6 9, .trans 2 10, .trans 3 0, .trans 1 2,
        .trans 1 7, .trans 5 10, .trans 10 3, .trans 9 0, .trans 0 5, .trans 5 1,
        .trans 1 11, .trans 0 4, .trans 4 3, .trans 9 6, .trans 3 6, .trans 6 0,
        .trans 0 2, .trans 2 3, .trans 11 9, .trans 10 1, .trans 1 4, .trans 3 8,
        .trans 1 7, .trans 7 0, .trans 0 7, .trans 0 11, .trans 2 11, .trans 5 0,
        .trans 5 7, .trans 5 11, .trans 7 5, .trans 7 8, .trans 8 2, .trans 8 4,
        .trans 8 11, .trans 9 4, .trans 11 4, .trans 11 9],
    .letter (.xi),
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR88nTGPlan_word : planWord wR8fR88nTGPlan = wR8fR88nTG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR88nTGPlan_ok : planOk wR8fR88nTGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR88nTHX : List SVec := tensorPlanF 64 wR8fR88nTHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR88nTGX : List SVec := tensorPlanF 64 wR8fR88nTGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wR8fR88nTL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR88nTH, ShortData.ofList wR8fR88nTHT, (1 / 128),
    tensorRat 64 wR8fR88nTHX ((tensorWordDenAll wR8fR88nTH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR88nTW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wR8fR88nTG, ShortData.ofList wR8fR88nTGT, (1 / 128),
    tensorRat 64 wR8fR88nTGX ((tensorWordDenAll wR8fR88nTG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR88nTH_check : wR8fR88nTHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR88nTD_ok : wR8fR88nTHD.ok = true ∧ wR8fR88nTGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR88nTHD_cols : ∀ i : Fin 24, qmWordP (wR8fR88nTHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR88nTHD.colsP i.val, wR8fR88nTHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR88nTHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR88nTHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR88nTHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR88nTHT_check : shortCheckF wR8fR88nTHD srcRootEightCShort.flat wR8fR88nTHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR88nTT_labels : wR8fR88nTHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR88nTGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR88nTH_growth : tensorWordGrowthAll wR8fR88nTH * 15 = 64424509440 := by decide

/-- The word bound of the target word. -/
theorem wR8fR88nTG_growth : tensorWordGrowthAll wR8fR88nTG * 15 = 515396075520 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR88nTL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR88nTH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR88nTL.real := by
  have hT := (tensorPlanF_actual wR8fR88nTHPlan wR8fR88nTHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR88nTHPlan_word, wR8fR88nTH_growth]; norm_num) 32).2
  rw [wR8fR88nTHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR88nTHW wR8fR88nTH_check wR8fR88nTHD
      wR8fR88nTD_ok.1 wR8fR88nTHD_cols
    wR8fR88nTHD_rows wR8fR88nTHT wR8fR88nTHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
