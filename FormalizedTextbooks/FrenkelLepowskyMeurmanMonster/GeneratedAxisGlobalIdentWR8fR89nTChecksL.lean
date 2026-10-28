/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR89nTData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[17]- <-> Tenth[60]+
(record r8f:R89-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR89nTChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR89nTH : List IdentLetter := wR8fR89nTHW.map Prod.fst

/-- The target word. -/
def wR8fR89nTG : List IdentLetter := wR8fR89nTGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR89nTH`. -/
def wR8fR89nTHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
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
theorem wR8fR89nTHPlan_word : planWord wR8fR89nTHPlan = wR8fR89nTH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR89nTHPlan_ok : planOk wR8fR89nTHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR89nTG`. -/
def wR8fR89nTGPlan : List TPlan :=
  [.letter (.qel (qmElt (4652755, false))),
    .letter (.sign 1991 0),
    .run
      [(0, true), (1, false), (0, false), (0, false), (1, false), (0, false), (1, false),
        (0, true), (1, false), (0, false), (0, false), (1, false), (0, true), (1, false),
        (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (1, true), (0, false), (0, false), (0, false),
        (1, true), (0, false), (0, false), (0, false), (1, true), (0, true), (0, true),
        (1, true), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, true), (0, true), (0, true), (0, true), (1, false),
        (0, false), (1, false), (0, false), (0, false), (0, false), (1, false),
        (0, false), (1, false), (0, false), (0, false), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (0, true)]
      [.trans 0 7, .trans 4 0, .trans 9 10, .trans 0 6, .trans 5 8, .trans 0 3, .trans 1 5,
        .trans 10 6, .trans 10 9, .trans 10 11, .trans 7 9, .trans 2 8, .trans 5 1,
        .trans 1 5, .trans 3 2, .trans 2 0, .trans 9 10, .trans 6 8, .trans 8 1,
        .trans 8 5, .trans 5 0, .trans 1 2, .trans 2 4, .trans 0 3, .trans 10 4,
        .trans 0 7, .trans 7 6, .trans 7 8, .trans 9 1, .trans 8 4, .trans 4 6,
        .trans 6 2, .trans 6 5, .trans 4 3, .trans 3 1, .trans 1 2],
    .letter (.xi),
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
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.sign 16 0),
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR89nTGPlan_word : planWord wR8fR89nTGPlan = wR8fR89nTG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR89nTGPlan_ok : planOk wR8fR89nTGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR89nTHX : List SVec := tensorPlanF 64 wR8fR89nTHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR89nTGX : List SVec := tensorPlanF 64 wR8fR89nTGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wR8fR89nTL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR89nTH, ShortData.ofList wR8fR89nTHT, (1 / 128),
    tensorRat 64 wR8fR89nTHX ((tensorWordDenAll wR8fR89nTH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR89nTW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wR8fR89nTG, ShortData.ofList wR8fR89nTGT, (1 / 128),
    tensorRat 64 wR8fR89nTGX ((tensorWordDenAll wR8fR89nTG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR89nTH_check : wR8fR89nTHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR89nTD_ok : wR8fR89nTHD.ok = true ∧ wR8fR89nTGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR89nTHD_cols : ∀ i : Fin 24, qmWordP (wR8fR89nTHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR89nTHD.colsP i.val, wR8fR89nTHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR89nTHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR89nTHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR89nTHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR89nTHT_check : shortCheckF wR8fR89nTHD srcRootEightCShort.flat wR8fR89nTHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR89nTT_labels : wR8fR89nTHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR89nTGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR89nTH_growth : tensorWordGrowthAll wR8fR89nTH * 15 = 983040 := by decide

/-- The word bound of the target word. -/
theorem wR8fR89nTG_growth : tensorWordGrowthAll wR8fR89nTG * 15 = 1055531162664960 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR89nTL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR89nTH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR89nTL.real := by
  have hT := (tensorPlanF_actual wR8fR89nTHPlan wR8fR89nTHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR89nTHPlan_word, wR8fR89nTH_growth]; norm_num) 32).2
  rw [wR8fR89nTHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR89nTHW wR8fR89nTH_check wR8fR89nTHD
      wR8fR89nTD_ok.1 wR8fR89nTHD_cols
    wR8fR89nTHD_rows wR8fR89nTHT wR8fR89nTHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
