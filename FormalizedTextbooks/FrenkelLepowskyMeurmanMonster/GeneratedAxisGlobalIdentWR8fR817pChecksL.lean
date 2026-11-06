/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Root8[26]+ <-> Root8[26]+
(record r8f:R817+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR817pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR817pH : List IdentLetter := wR8fR817pHW.map Prod.fst

/-- The target word. -/
def wR8fR817pG : List IdentLetter := wR8fR817pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR817pH`. -/
def wR8fR817pHPlan : List TPlan :=
  [.letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (1, true), (0, true)]
      [.trans 6 5, .trans 10 1, .trans 4 7, .trans 4 10, .trans 3 4, .trans 10 2, .trans 5 3,
        .trans 9 6, .trans 8 6, .trans 0 5, .trans 0 2, .trans 2 11, .trans 5 1,
        .trans 5 8, .trans 8 9, .trans 9 4, .trans 4 9, .trans 4 7, .trans 4 10,
        .trans 3 0, .trans 0 3, .trans 1 2, .trans 2 4, .trans 7 3, .trans 3 7,
        .trans 3 8, .trans 3 9, .trans 3 11, .trans 6 4, .trans 4 6, .trans 4 8,
        .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 10, .trans 7 0, .trans 10 4,
        .trans 10 8, .trans 10 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR817pHPlan_word : planWord wR8fR817pHPlan = wR8fR817pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR817pHPlan_ok : planOk wR8fR817pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR817pG`. -/
def wR8fR817pGPlan : List TPlan :=
  [.letter (.qel (qmElt (15521521, true))),
    .letter (.sign 1777 0),
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (1, true), (0, true)]
      [.trans 6 5, .trans 10 1, .trans 4 7, .trans 4 10, .trans 3 4, .trans 10 2, .trans 5 3,
        .trans 9 6, .trans 8 6, .trans 0 5, .trans 0 2, .trans 2 11, .trans 5 1,
        .trans 5 8, .trans 8 9, .trans 9 4, .trans 4 9, .trans 4 7, .trans 4 10,
        .trans 3 0, .trans 0 3, .trans 1 2, .trans 2 4, .trans 7 3, .trans 3 7,
        .trans 3 8, .trans 3 9, .trans 3 11, .trans 6 4, .trans 4 6, .trans 4 8,
        .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 10, .trans 7 0, .trans 10 4,
        .trans 10 8, .trans 10 11]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR817pGPlan_word : planWord wR8fR817pGPlan = wR8fR817pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR817pGPlan_ok : planOk wR8fR817pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR817pHX : List SVec := tensorPlanF 64 wR8fR817pHPlan (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR817pGX : List SVec := tensorPlanF 64 wR8fR817pGPlan (rootEightSrcXL 64)

/-- The representation of the source image. -/
def wR8fR817pL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR817pH, ShortData.ofList wR8fR817pHT, (1 / 128),
    tensorRat 64 wR8fR817pHX ((tensorWordDenAll wR8fR817pH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR817pW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR817pG, ShortData.ofList wR8fR817pGT, (1 / 128),
    tensorRat 64 wR8fR817pGX ((tensorWordDenAll wR8fR817pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR817pH_check : wR8fR817pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR817pD_ok : wR8fR817pHD.ok = true ∧ wR8fR817pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR817pHD_cols : ∀ i : Fin 24, qmWordP (wR8fR817pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR817pHD.colsP i.val, wR8fR817pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR817pHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR817pHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR817pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR817pHT_check : shortCheckF wR8fR817pHD srcRootEightCShort.flat wR8fR817pHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR817pT_labels : wR8fR817pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR817pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR817pH_growth : tensorWordGrowthAll wR8fR817pH * 15 = 983040 := by decide

/-- The word bound of the target word. -/
theorem wR8fR817pG_growth : tensorWordGrowthAll wR8fR817pG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR817pL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR817pH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR817pL.real := by
  have hT := (tensorPlanF_actual wR8fR817pHPlan wR8fR817pHPlan_ok (rootEightSrcXL_bnd (w := 64)
      (by norm_num))
    (by rw [wR8fR817pHPlan_word, wR8fR817pH_growth]; norm_num) 32).2
  rw [wR8fR817pHPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR817pHW wR8fR817pH_check wR8fR817pHD
      wR8fR817pD_ok.1 wR8fR817pHD_cols
    wR8fR817pHD_rows wR8fR817pHT wR8fR817pHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
