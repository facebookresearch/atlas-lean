/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[4]- <-> Root8[4]-
(record r8f:R822-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR822nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR822nH : List IdentLetter := wR8fR822nHW.map Prod.fst

/-- The target word. -/
def wR8fR822nG : List IdentLetter := wR8fR822nGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR822nH`. -/
def wR8fR822nHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(0, false), (1, true), (0, true), (1, true)]
      [.trans 0 4, .trans 6 2, .trans 0 7, .trans 0 3, .trans 3 6, .trans 9 10, .trans 5 1,
        .trans 9 7, .trans 3 11, .trans 7 5, .trans 10 0, .trans 7 11, .trans 2 3,
        .trans 8 9, .trans 2 0, .trans 3 5, .trans 8 4, .trans 1 5, .trans 5 3,
        .trans 1 0, .trans 6 0, .trans 5 2, .trans 2 8, .trans 8 7, .trans 0 1,
        .trans 0 3, .trans 8 2, .trans 0 5, .trans 8 5, .trans 7 10, .trans 10 9,
        .trans 9 1, .trans 1 11, .trans 4 6, .trans 6 9, .trans 9 4, .trans 9 6],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR822nHPlan_word : planWord wR8fR822nHPlan = wR8fR822nH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR822nHPlan_ok : planOk wR8fR822nHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR822nG`. -/
def wR8fR822nGPlan : List TPlan :=
  [.letter (.qel (qmElt (10399744, false))),
    .letter (.sign 361 0),
    .letter (.xi),
    .run
      [(0, false), (1, true), (0, true), (1, true)]
      [.trans 0 4, .trans 6 2, .trans 0 7, .trans 0 3, .trans 3 6, .trans 9 10, .trans 5 1,
        .trans 9 7, .trans 3 11, .trans 7 5, .trans 10 0, .trans 7 11, .trans 2 3,
        .trans 8 9, .trans 2 0, .trans 3 5, .trans 8 4, .trans 1 5, .trans 5 3,
        .trans 1 0, .trans 6 0, .trans 5 2, .trans 2 8, .trans 8 7, .trans 0 1,
        .trans 0 3, .trans 8 2, .trans 0 5, .trans 8 5, .trans 7 10, .trans 10 9,
        .trans 9 1, .trans 1 11, .trans 4 6, .trans 6 9, .trans 9 4, .trans 9 6],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR822nGPlan_word : planWord wR8fR822nGPlan = wR8fR822nG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR822nGPlan_ok : planOk wR8fR822nGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR822nHX : List SVec := tensorPlanF 64 wR8fR822nHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR822nGX : List SVec := tensorPlanF 64 wR8fR822nGPlan (rootEightSrcXL 64)

/-- The representation of the source image. -/
def wR8fR822nL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR822nH, ShortData.ofList wR8fR822nHT, (1 / 128),
    tensorRat 64 wR8fR822nHX ((tensorWordDenAll wR8fR822nH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR822nW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR822nG, ShortData.ofList wR8fR822nGT, (1 / 128),
    tensorRat 64 wR8fR822nGX ((tensorWordDenAll wR8fR822nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR822nH_check : wR8fR822nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR822nD_ok : wR8fR822nHD.ok = true ∧ wR8fR822nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR822nHD_cols : ∀ i : Fin 24, qmWordP (wR8fR822nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR822nHD.colsP i.val, wR8fR822nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR822nHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR822nHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR822nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR822nHT_check : shortCheckF wR8fR822nHD srcRootEightCShort.flat wR8fR822nHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR822nT_labels : wR8fR822nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR822nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR822nH_growth : tensorWordGrowthAll wR8fR822nH * 15 = 983040 := by decide

/-- The word bound of the target word. -/
theorem wR8fR822nG_growth : tensorWordGrowthAll wR8fR822nG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR822nL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR822nH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR822nL.real := by
  have hT := (tensorPlanF_actual wR8fR822nHPlan wR8fR822nHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR822nHPlan_word, wR8fR822nH_growth]; norm_num) 32).2
  rw [wR8fR822nHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR822nHW wR8fR822nH_check wR8fR822nHD
      wR8fR822nD_ok.1 wR8fR822nHD_cols
    wR8fR822nHD_rows wR8fR822nHT wR8fR822nHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
