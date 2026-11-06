/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR811nTData
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
`GeneratedAxisGlobalIdentWR8fR811nTChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR811nTH : List IdentLetter := wR8fR811nTHW.map Prod.fst

/-- The target word. -/
def wR8fR811nTG : List IdentLetter := wR8fR811nTGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR811nTH`. -/
def wR8fR811nTHPlan : List TPlan :=
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
theorem wR8fR811nTHPlan_word : planWord wR8fR811nTHPlan = wR8fR811nTH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR811nTHPlan_ok : planOk wR8fR811nTHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR811nTG`. -/
def wR8fR811nTGPlan : List TPlan :=
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
theorem wR8fR811nTGPlan_word : planWord wR8fR811nTGPlan = wR8fR811nTG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR811nTGPlan_ok : planOk wR8fR811nTGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR811nTHX : List SVec := tensorPlanF 64 wR8fR811nTHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR811nTGX : List SVec := tensorPlanF 64 wR8fR811nTGPlan (rootEightSrcXL 64)

/-- The representation of the source image. -/
def wR8fR811nTL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR811nTH, ShortData.ofList wR8fR811nTHT, (1 / 128),
    tensorRat 64 wR8fR811nTHX ((tensorWordDenAll wR8fR811nTH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR811nTW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR811nTG, ShortData.ofList wR8fR811nTGT, (1 / 128),
    tensorRat 64 wR8fR811nTGX ((tensorWordDenAll wR8fR811nTG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR811nTH_check : wR8fR811nTHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR811nTD_ok : wR8fR811nTHD.ok = true ∧ wR8fR811nTGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR811nTHD_cols : ∀ i : Fin 24, qmWordP (wR8fR811nTHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR811nTHD.colsP i.val, wR8fR811nTHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR811nTHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR811nTHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR811nTHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR811nTHT_check : shortCheckF wR8fR811nTHD srcRootEightCShort.flat wR8fR811nTHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR811nTT_labels : wR8fR811nTHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR811nTGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR811nTH_growth : tensorWordGrowthAll wR8fR811nTH * 15 = 2013265920 := by decide

/-- The word bound of the target word. -/
theorem wR8fR811nTG_growth : tensorWordGrowthAll wR8fR811nTG * 15 = 16106127360 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR811nTL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR811nTH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR811nTL.real := by
  have hT := (tensorPlanF_actual wR8fR811nTHPlan wR8fR811nTHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR811nTHPlan_word, wR8fR811nTH_growth]; norm_num) 32).2
  rw [wR8fR811nTHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR811nTHW wR8fR811nTH_check wR8fR811nTHD
      wR8fR811nTD_ok.1 wR8fR811nTHD_cols
    wR8fR811nTHD_rows wR8fR811nTHT wR8fR811nTHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
