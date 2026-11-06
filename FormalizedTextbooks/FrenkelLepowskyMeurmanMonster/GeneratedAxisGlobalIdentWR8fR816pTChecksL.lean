/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[22]+ <-> Root8[22]+
(record r8f:R816+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR816pTChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR816pTH : List IdentLetter := wR8fR816pTHW.map Prod.fst

/-- The target word. -/
def wR8fR816pTG : List IdentLetter := wR8fR816pTGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR816pTH`. -/
def wR8fR816pTHPlan : List TPlan :=
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
        .trans 9 11, .trans 9 2, .trans 8 11],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR816pTHPlan_word : planWord wR8fR816pTHPlan = wR8fR816pTH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR816pTHPlan_ok : planOk wR8fR816pTHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR816pTG`. -/
def wR8fR816pTGPlan : List TPlan :=
  [.letter (.qel (qmElt (16054056, true))),
    .letter (.sign 1832 0),
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
      [(0, false)]
      [.trans 0 11, .trans 0 10, .trans 8 3, .trans 9 11, .trans 7 6, .trans 7 0, .trans 0 1,
        .trans 5 0, .trans 8 2, .trans 9 2, .trans 10 6, .trans 10 4, .trans 0 8,
        .trans 6 7, .trans 4 5, .trans 7 3, .trans 10 1, .trans 4 3, .trans 5 2,
        .trans 6 2, .trans 2 9, .trans 9 8, .trans 1 8, .trans 8 3, .trans 3 9,
        .trans 9 11, .trans 9 2, .trans 8 11],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR816pTGPlan_word : planWord wR8fR816pTGPlan = wR8fR816pTG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR816pTGPlan_ok : planOk wR8fR816pTGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR816pTHX : List SVec := tensorPlanF 64 wR8fR816pTHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR816pTGX : List SVec := tensorPlanF 64 wR8fR816pTGPlan (rootEightSrcXL 64)

/-- The representation of the source image. -/
def wR8fR816pTL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR816pTH, ShortData.ofList wR8fR816pTHT, (1 / 128),
    tensorRat 64 wR8fR816pTHX ((tensorWordDenAll wR8fR816pTH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR816pTW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR816pTG, ShortData.ofList wR8fR816pTGT, (1 / 128),
    tensorRat 64 wR8fR816pTGX ((tensorWordDenAll wR8fR816pTG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR816pTH_check : wR8fR816pTHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR816pTD_ok : wR8fR816pTHD.ok = true ∧ wR8fR816pTGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR816pTHD_cols : ∀ i : Fin 24, qmWordP (wR8fR816pTHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR816pTHD.colsP i.val, wR8fR816pTHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR816pTHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR816pTHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR816pTHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR816pTHT_check : shortCheckF wR8fR816pTHD srcRootEightCShort.flat wR8fR816pTHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR816pTT_labels : wR8fR816pTHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR816pTGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR816pTH_growth : tensorWordGrowthAll wR8fR816pTH * 15 = 16492674416640 := by decide

/-- The word bound of the target word. -/
theorem wR8fR816pTG_growth : tensorWordGrowthAll wR8fR816pTG * 15 = 131941395333120 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR816pTL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR816pTH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR816pTL.real := by
  have hT := (tensorPlanF_actual wR8fR816pTHPlan wR8fR816pTHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR816pTHPlan_word, wR8fR816pTH_growth]; norm_num) 32).2
  rw [wR8fR816pTHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR816pTHW wR8fR816pTH_check wR8fR816pTHD
      wR8fR816pTD_ok.1 wR8fR816pTHD_cols
    wR8fR816pTHD_rows wR8fR816pTHT wR8fR816pTHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
