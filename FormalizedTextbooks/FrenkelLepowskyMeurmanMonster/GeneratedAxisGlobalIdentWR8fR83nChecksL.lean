/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[11]- <-> Twelfth[29]-
(record r8f:R83-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR83nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR83nH : List IdentLetter := wR8fR83nHW.map Prod.fst

/-- The target word. -/
def wR8fR83nG : List IdentLetter := wR8fR83nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR83nH`. -/
def wR8fR83nHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR83nHPlan_word : planWord wR8fR83nHPlan = wR8fR83nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR83nHPlan_ok : planOk wR8fR83nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR83nG`. -/
def wR8fR83nGPlan : List TPlan :=
  [.letter (.qel (qmElt (16715351, false))),
    .letter (.sign 933 0),
    .run
      [(0, true), (1, false), (0, true), (0, true), (1, false), (0, true), (0, true),
        (1, false), (0, false), (1, false), (0, true), (1, false), (0, false),
        (0, false), (1, false), (0, false), (0, false), (0, false), (1, false),
        (0, true), (1, false), (0, true), (1, false), (0, false), (0, false), (1, false),
        (0, false), (0, false), (1, false), (0, false), (0, false), (1, false)]
      [.trans 10 5, .trans 10 8, .trans 7 2, .trans 5 1, .trans 10 11, .trans 4 6, .trans 0 5,
        .trans 2 10, .trans 10 4, .trans 6 4, .trans 4 3, .trans 3 9, .trans 8 3,
        .trans 8 11, .trans 8 9, .trans 7 0, .trans 4 0, .trans 7 6, .trans 6 10,
        .trans 10 2, .trans 2 5, .trans 0 6, .trans 0 7, .trans 1 6, .trans 3 8,
        .trans 4 10, .trans 5 4, .trans 5 7, .trans 5 10, .trans 6 3, .trans 6 8,
        .trans 6 10, .trans 6 11, .trans 8 0, .trans 8 2, .trans 8 3, .trans 8 6,
        .trans 8 7, .trans 8 10, .trans 9 1, .trans 9 2, .trans 9 6, .trans 9 8,
        .trans 9 10, .trans 10 1, .trans 10 4, .trans 10 5, .trans 10 6, .trans 10 7,
        .trans 10 8, .trans 10 9],
    .letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi),
    .run
      [(0, false), (0, false)]
      [.trans 9 2, .trans 0 11, .trans 0 4, .trans 4 9, .trans 4 6, .trans 7 8, .trans 8 3,
        .trans 3 11, .trans 10 4, .trans 4 1, .trans 6 7, .trans 0 2, .trans 7 6,
        .trans 7 1, .trans 0 7, .trans 7 0, .trans 1 11, .trans 1 8, .trans 8 2,
        .trans 3 2, .trans 2 8, .trans 4 7, .trans 4 8, .trans 5 10, .trans 6 10,
        .trans 7 9, .trans 8 3, .trans 8 9, .trans 9 11, .trans 10 3, .trans 10 4,
        .trans 10 5, .trans 10 6, .trans 10 7, .trans 10 8],
    .letter (.sign 16 0)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR83nGPlan_word : planWord wR8fR83nGPlan = wR8fR83nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR83nGPlan_ok : planOk wR8fR83nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR83nHX : List SVec := tensorPlanF 72 wR8fR83nHPlan (rootEightSrcXL 72)

/-- The packed tensor of the target image. -/
def wR8fR83nGX : List SVec := tensorPlanF 72 wR8fR83nGPlan (twelfthSrcXW 72)

/-- The representation of the source image. -/
def wR8fR83nL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR83nH, ShortData.ofList wR8fR83nHT, (1 / 128),
    tensorRat 72 wR8fR83nHX ((tensorWordDenAll wR8fR83nH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR83nW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet wR8fR83nG, ShortData.ofList wR8fR83nGT, (1 / 128),
    tensorRat 72 wR8fR83nGX ((tensorWordDenAll wR8fR83nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR83nH_check : wR8fR83nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR83nD_ok : wR8fR83nHD.ok = true ∧ wR8fR83nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR83nHD_cols : ∀ i : Fin 24, qmWordP (wR8fR83nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR83nHD.colsP i.val, wR8fR83nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR83nHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR83nHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR83nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR83nHT_check : shortCheckF wR8fR83nHD srcRootEightCShort.flat wR8fR83nHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR83nT_labels : wR8fR83nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR83nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR83nH_growth : tensorWordGrowthAll wR8fR83nH * 15 = 983040 := by decide

/-- The word bound of the target word. -/
theorem wR8fR83nG_growth : tensorWordGrowthAll wR8fR83nG * 15 = 62914560 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR83nL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR83nH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR83nL.real := by
  have hT := (tensorPlanF_actual wR8fR83nHPlan wR8fR83nHPlan_ok (rootEightSrcXL_bnd (w := 72) (by
      norm_num))
    (by rw [wR8fR83nHPlan_word, wR8fR83nH_growth]; norm_num) 32).2
  rw [wR8fR83nHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 72) wR8fR83nHW wR8fR83nH_check wR8fR83nHD
      wR8fR83nD_ok.1 wR8fR83nHD_cols
    wR8fR83nHD_rows wR8fR83nHT wR8fR83nHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
