/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR811nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[13]- <-> Root8[13]-
(record r8f:R811-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR811nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR811nH : List IdentLetter := wR8fR811nHW.map Prod.fst

/-- The target word. -/
def wR8fR811nG : List IdentLetter := wR8fR811nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR811nH`. -/
def wR8fR811nHPlan : List TPlan :=
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
    .letter (.sign 16 0)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR811nHPlan_word : planWord wR8fR811nHPlan = wR8fR811nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR811nHPlan_ok : planOk wR8fR811nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR811nG`. -/
def wR8fR811nGPlan : List TPlan :=
  [.letter (.qel (qmElt (14354580, false))),
    .letter (.sign 1940 0),
    .run
      [(0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false),
        (1, false), (0, true), (0, true), (1, false), (0, true), (1, false), (0, false),
        (1, false), (0, false), (0, false), (1, false), (0, false), (0, false),
        (0, false), (1, false), (0, true), (0, true), (0, true), (1, true), (0, false),
        (1, true), (0, false), (0, false), (0, false), (1, true), (0, true), (1, true),
        (0, true), (0, true), (0, true), (1, true), (0, false), (1, true), (0, true),
        (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (0, false), (1, false), (0, true),
        (1, false), (0, false), (0, false), (1, false), (0, true), (1, false),
        (0, false), (0, false), (1, false), (0, true), (1, false), (0, false),
        (1, false), (0, false)]
      [.trans 2 3, .trans 1 2, .trans 1 0, .trans 8 6, .trans 6 2, .trans 10 4, .trans 9 7,
        .trans 7 0, .trans 7 3, .trans 3 2, .trans 9 2, .trans 10 1, .trans 4 6,
        .trans 2 3, .trans 5 7, .trans 7 1],
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
    .letter (.sign 16 0)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR811nGPlan_word : planWord wR8fR811nGPlan = wR8fR811nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR811nGPlan_ok : planOk wR8fR811nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR811nHX : List SVec := tensorPlanF 64 wR8fR811nHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR811nGX : List SVec := tensorPlanF 64 wR8fR811nGPlan (rootEightSrcXL 64)

/-- The representation of the source image. -/
def wR8fR811nL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR811nH, ShortData.ofList wR8fR811nHT, (1 / 128),
    tensorRat 64 wR8fR811nHX ((tensorWordDenAll wR8fR811nH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR811nW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR811nG, ShortData.ofList wR8fR811nGT, (1 / 128),
    tensorRat 64 wR8fR811nGX ((tensorWordDenAll wR8fR811nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR811nH_check : wR8fR811nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR811nD_ok : wR8fR811nHD.ok = true ∧ wR8fR811nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR811nHD_cols : ∀ i : Fin 24, qmWordP (wR8fR811nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR811nHD.colsP i.val, wR8fR811nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR811nHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR811nHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR811nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR811nHT_check : shortCheckF wR8fR811nHD srcRootEightCShort.flat wR8fR811nHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR811nT_labels : wR8fR811nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR811nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR811nH_growth : tensorWordGrowthAll wR8fR811nH * 15 = 2013265920 := by decide

/-- The word bound of the target word. -/
theorem wR8fR811nG_growth : tensorWordGrowthAll wR8fR811nG * 15 = 16106127360 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR811nL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR811nH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR811nL.real := by
  have hT := (tensorPlanF_actual wR8fR811nHPlan wR8fR811nHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR811nHPlan_word, wR8fR811nH_growth]; norm_num) 32).2
  rw [wR8fR811nHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR811nHW wR8fR811nH_check wR8fR811nHD
      wR8fR811nD_ok.1 wR8fR811nHD_cols
    wR8fR811nHD_rows wR8fR811nHT wR8fR811nHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
