/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pData
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
`GeneratedAxisGlobalIdentWR8fR816pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR816pH : List IdentLetter := wR8fR816pHW.map Prod.fst

/-- The target word. -/
def wR8fR816pG : List IdentLetter := wR8fR816pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR816pH`. -/
def wR8fR816pHPlan : List TPlan :=
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
theorem wR8fR816pHPlan_word : planWord wR8fR816pHPlan = wR8fR816pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR816pHPlan_ok : planOk wR8fR816pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR816pG`. -/
def wR8fR816pGPlan : List TPlan :=
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
theorem wR8fR816pGPlan_word : planWord wR8fR816pGPlan = wR8fR816pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR816pGPlan_ok : planOk wR8fR816pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR816pHX : List SVec := tensorPlanF 64 wR8fR816pHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR816pGX : List SVec := tensorPlanF 64 wR8fR816pGPlan (rootEightSrcXL 64)

/-- The representation of the source image. -/
def wR8fR816pL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR816pH, ShortData.ofList wR8fR816pHT, (1 / 128),
    tensorRat 64 wR8fR816pHX ((tensorWordDenAll wR8fR816pH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR816pW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR816pG, ShortData.ofList wR8fR816pGT, (1 / 128),
    tensorRat 64 wR8fR816pGX ((tensorWordDenAll wR8fR816pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR816pH_check : wR8fR816pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR816pD_ok : wR8fR816pHD.ok = true ∧ wR8fR816pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR816pHD_cols : ∀ i : Fin 24, qmWordP (wR8fR816pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR816pHD.colsP i.val, wR8fR816pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR816pHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR816pHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR816pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR816pHT_check : shortCheckF wR8fR816pHD srcRootEightCShort.flat wR8fR816pHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR816pT_labels : wR8fR816pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR816pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR816pH_growth : tensorWordGrowthAll wR8fR816pH * 15 = 16492674416640 := by decide

/-- The word bound of the target word. -/
theorem wR8fR816pG_growth : tensorWordGrowthAll wR8fR816pG * 15 = 131941395333120 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR816pL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR816pH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR816pL.real := by
  have hT := (tensorPlanF_actual wR8fR816pHPlan wR8fR816pHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR816pHPlan_word, wR8fR816pH_growth]; norm_num) 32).2
  rw [wR8fR816pHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR816pHW wR8fR816pH_check wR8fR816pHD
      wR8fR816pD_ok.1 wR8fR816pHD_cols
    wR8fR816pHD_rows wR8fR816pHT wR8fR816pHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
