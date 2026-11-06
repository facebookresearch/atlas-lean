/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82nTData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[2]- <-> Tenth[38]+
(record r8f:R82-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR82nTChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR82nTH : List IdentLetter := wR8fR82nTHW.map Prod.fst

/-- The target word. -/
def wR8fR82nTG : List IdentLetter := wR8fR82nTGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR82nTH`. -/
def wR8fR82nTHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR82nTHPlan_word : planWord wR8fR82nTHPlan = wR8fR82nTH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR82nTHPlan_ok : planOk wR8fR82nTHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR82nTG`. -/
def wR8fR82nTGPlan : List TPlan :=
  [.letter (.qel (qmElt (3183047, false))),
    .letter (.sign 476 0),
    .run
      [(0, true), (0, true), (1, false), (0, true), (0, true), (0, true), (1, false),
        (0, true), (0, true), (1, false), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, true), (1, true), (0, false), (0, false), (1, true), (0, true), (1, true),
        (0, true), (1, true), (0, false), (0, false), (1, true), (0, true), (0, true),
        (1, true), (0, false), (0, false), (1, true), (0, true), (1, true), (0, true),
        (1, false), (0, false), (0, false), (1, false), (0, true), (0, true), (1, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, false), (1, false), (0, true), (0, true)]
      [.trans 1 0, .trans 0 1, .trans 0 2, .trans 0 11, .trans 3 1, .trans 1 3, .trans 1 5,
        .trans 1 6, .trans 1 7, .trans 1 11, .trans 5 2, .trans 2 0, .trans 2 5,
        .trans 2 6, .trans 2 7, .trans 8 3, .trans 3 0, .trans 3 8, .trans 4 0,
        .trans 4 1, .trans 4 5, .trans 4 7, .trans 4 8, .trans 4 9, .trans 4 10,
        .trans 5 0, .trans 5 2, .trans 5 6, .trans 5 7, .trans 5 8, .trans 5 9,
        .trans 5 10, .trans 9 6, .trans 6 3, .trans 6 5, .trans 6 9, .trans 6 10,
        .trans 6 11, .trans 7 0, .trans 7 2, .trans 7 4, .trans 7 5, .trans 7 6,
        .trans 7 9, .trans 10 8, .trans 8 3, .trans 8 7, .trans 8 10, .trans 8 11,
        .trans 10 9, .trans 9 0, .trans 9 1, .trans 9 2, .trans 9 4, .trans 9 5,
        .trans 9 7, .trans 9 8, .trans 9 10, .trans 9 11, .trans 10 6, .trans 10 7,
        .trans 10 8, .trans 10 11],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.xi),
    .letter (.xi),
    .letter (.sign 16 0),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi),
    .letter (.xi),
    .letter (.sign 32 0)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR82nTGPlan_word : planWord wR8fR82nTGPlan = wR8fR82nTG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR82nTGPlan_ok : planOk wR8fR82nTGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR82nTHX : List SVec := tensorPlanF 64 wR8fR82nTHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR82nTGX : List SVec := tensorPlanF 64 wR8fR82nTGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wR8fR82nTL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR82nTH, ShortData.ofList wR8fR82nTHT, (1 / 128),
    tensorRat 64 wR8fR82nTHX ((tensorWordDenAll wR8fR82nTH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR82nTW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wR8fR82nTG, ShortData.ofList wR8fR82nTGT, (1 / 128),
    tensorRat 64 wR8fR82nTGX ((tensorWordDenAll wR8fR82nTG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR82nTH_check : wR8fR82nTHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR82nTD_ok : wR8fR82nTHD.ok = true ∧ wR8fR82nTGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR82nTHD_cols : ∀ i : Fin 24, qmWordP (wR8fR82nTHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR82nTHD.colsP i.val, wR8fR82nTHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR82nTHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR82nTHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR82nTHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR82nTHT_check : shortCheckF wR8fR82nTHD srcRootEightCShort.flat wR8fR82nTHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR82nTT_labels : wR8fR82nTHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR82nTGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR82nTH_growth : tensorWordGrowthAll wR8fR82nTH * 15 = 251658240 := by decide

/-- The word bound of the target word. -/
theorem wR8fR82nTG_growth : tensorWordGrowthAll wR8fR82nTG * 15 = 2161727821137838080 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR82nTL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR82nTH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR82nTL.real := by
  have hT := (tensorPlanF_actual wR8fR82nTHPlan wR8fR82nTHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR82nTHPlan_word, wR8fR82nTH_growth]; norm_num) 32).2
  rw [wR8fR82nTHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR82nTHW wR8fR82nTH_check wR8fR82nTHD
      wR8fR82nTD_ok.1 wR8fR82nTHD_cols
    wR8fR82nTHD_rows wR8fR82nTHT wR8fR82nTHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
