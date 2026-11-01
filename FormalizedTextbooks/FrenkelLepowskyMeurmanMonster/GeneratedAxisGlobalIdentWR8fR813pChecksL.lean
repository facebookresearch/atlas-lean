/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR813pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[7]+ <-> Root8[7]+
(record r8f:R813+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR813pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR813pH : List IdentLetter := wR8fR813pHW.map Prod.fst

/-- The target word. -/
def wR8fR813pG : List IdentLetter := wR8fR813pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR813pH`. -/
def wR8fR813pHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, true)]
      [.trans 9 5, .trans 6 1, .trans 10 6, .trans 8 7, .trans 10 4, .trans 0 6, .trans 0 11,
        .trans 7 2, .trans 2 9, .trans 2 8, .trans 8 10, .trans 6 0, .trans 6 9,
        .trans 4 7, .trans 7 8, .trans 5 8, .trans 8 5, .trans 0 10, .trans 9 10,
        .trans 0 3, .trans 5 3, .trans 10 2, .trans 0 6, .trans 10 3, .trans 3 11,
        .trans 3 5, .trans 5 0, .trans 5 1, .trans 1 4, .trans 1 11, .trans 0 8,
        .trans 0 9, .trans 0 11, .trans 2 7, .trans 2 11, .trans 4 2, .trans 4 7,
        .trans 4 11, .trans 7 0, .trans 7 6, .trans 7 8, .trans 7 9, .trans 7 11,
        .trans 8 2, .trans 8 4, .trans 8 11],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR813pHPlan_word : planWord wR8fR813pHPlan = wR8fR813pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR813pHPlan_ok : planOk wR8fR813pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR813pG`. -/
def wR8fR813pGPlan : List TPlan :=
  [.letter (.qel (qmElt (11882701, true))),
    .letter (.sign 203 0),
    .letter (.xi),
    .letter (.xi),
    .run
      [(1, true), (0, true)]
      [.trans 9 5, .trans 6 1, .trans 10 6, .trans 8 7, .trans 10 4, .trans 0 6, .trans 0 11,
        .trans 7 2, .trans 2 9, .trans 2 8, .trans 8 10, .trans 6 0, .trans 6 9,
        .trans 4 7, .trans 7 8, .trans 5 8, .trans 8 5, .trans 0 10, .trans 9 10,
        .trans 0 3, .trans 5 3, .trans 10 2, .trans 0 6, .trans 10 3, .trans 3 11,
        .trans 3 5, .trans 5 0, .trans 5 1, .trans 1 4, .trans 1 11, .trans 0 8,
        .trans 0 9, .trans 0 11, .trans 2 7, .trans 2 11, .trans 4 2, .trans 4 7,
        .trans 4 11, .trans 7 0, .trans 7 6, .trans 7 8, .trans 7 9, .trans 7 11,
        .trans 8 2, .trans 8 4, .trans 8 11],
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR813pGPlan_word : planWord wR8fR813pGPlan = wR8fR813pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR813pGPlan_ok : planOk wR8fR813pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR813pHX : List SVec := tensorPlanF 64 wR8fR813pHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR813pGX : List SVec := tensorPlanF 64 wR8fR813pGPlan (rootEightSrcXL 64)

/-- The representation of the source image. -/
def wR8fR813pL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR813pH, ShortData.ofList wR8fR813pHT, (1 / 128),
    tensorRat 64 wR8fR813pHX ((tensorWordDenAll wR8fR813pH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR813pW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR813pG, ShortData.ofList wR8fR813pGT, (1 / 128),
    tensorRat 64 wR8fR813pGX ((tensorWordDenAll wR8fR813pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR813pH_check : wR8fR813pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR813pD_ok : wR8fR813pHD.ok = true ∧ wR8fR813pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR813pHD_cols : ∀ i : Fin 24, qmWordP (wR8fR813pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR813pHD.colsP i.val, wR8fR813pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR813pHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR813pHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR813pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR813pHT_check : shortCheckF wR8fR813pHD srcRootEightCShort.flat wR8fR813pHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR813pT_labels : wR8fR813pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR813pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR813pH_growth : tensorWordGrowthAll wR8fR813pH * 15 = 251658240 := by decide

/-- The word bound of the target word. -/
theorem wR8fR813pG_growth : tensorWordGrowthAll wR8fR813pG * 15 = 2013265920 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR813pL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR813pH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR813pL.real := by
  have hT := (tensorPlanF_actual wR8fR813pHPlan wR8fR813pHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR813pHPlan_word, wR8fR813pH_growth]; norm_num) 32).2
  rw [wR8fR813pHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR813pHW wR8fR813pH_check wR8fR813pHD
      wR8fR813pD_ok.1 wR8fR813pHD_cols
    wR8fR813pHD_rows wR8fR813pHT wR8fR813pHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
