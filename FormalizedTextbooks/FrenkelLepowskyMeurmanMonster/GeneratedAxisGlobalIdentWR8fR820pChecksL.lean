/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Fourth[10]+ <-> Root8[25]+
(record r8f:R820+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR820pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR820pH : List IdentLetter := wR8fR820pHW.map Prod.fst

/-- The target word. -/
def wR8fR820pG : List IdentLetter := wR8fR820pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wR8fR820pG`. -/
def wR8fR820pGPlan : List TPlan :=
  [.letter (.qel (qmElt (14509896, false))),
    .letter (.sign 372 0),
    .run
      [(0, false), (1, false), (0, true), (0, true), (0, true), (1, false), (0, true),
        (1, false), (0, true), (0, true), (1, false), (0, false), (1, false), (0, true),
        (0, true), (1, false), (0, true), (0, true), (1, false), (0, false), (0, false),
        (1, false), (0, true), (1, false)]
      [.trans 4 5, .trans 10 3, .trans 0 2, .trans 7 1, .trans 4 10, .trans 1 4, .trans 6 7,
        .trans 8 4, .trans 7 8, .trans 8 7, .trans 7 2, .trans 2 10, .trans 10 1,
        .trans 1 0, .trans 6 9, .trans 5 10, .trans 10 2, .trans 2 6, .trans 6 3,
        .trans 2 9, .trans 3 1, .trans 1 5, .trans 5 8, .trans 5 1, .trans 10 11,
        .trans 4 9, .trans 8 0, .trans 0 6, .trans 9 3, .trans 5 3, .trans 9 6,
        .trans 6 7, .trans 9 11],
    .letter (.xi),
    .run
      [(1, false), (0, false), (0, false)]
      [.trans 6 2, .trans 10 5, .trans 1 6, .trans 1 7, .trans 5 4, .trans 0 11, .trans 0 9,
        .trans 7 8, .trans 9 10, .trans 10 1, .trans 8 10, .trans 0 7, .trans 5 11,
        .trans 1 3, .trans 3 8, .trans 8 10, .trans 1 6, .trans 6 4, .trans 4 0,
        .trans 0 7, .trans 0 3, .trans 2 8, .trans 8 7, .trans 8 11, .trans 7 4,
        .trans 5 9, .trans 0 1, .trans 9 5, .trans 4 1, .trans 1 9, .trans 4 6,
        .trans 6 5, .trans 5 2, .trans 6 9, .trans 5 8, .trans 9 10, .trans 8 10,
        .trans 10 2, .trans 2 3, .trans 3 11],
    .letter (.xi),
    .run
      [(1, false)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wR8fR820pGPlan_word : planWord wR8fR820pGPlan = wR8fR820pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wR8fR820pGPlan_ok : planOk wR8fR820pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wR8fR820pHX : List SVec := tensorWordAll 64 wR8fR820pH (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR820pGX : List SVec := tensorPlanF 64 wR8fR820pGPlan (fourthSrcXW 64)

/-- The representation of the source image. -/
def wR8fR820pL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR820pH, ShortData.ofList wR8fR820pHT, (1 / 128),
    tensorRat 64 wR8fR820pHX ((tensorWordDenAll wR8fR820pH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR820pW : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet wR8fR820pG, ShortData.ofList wR8fR820pGT, 1 / 8,
    tensorRat 64 wR8fR820pGX ((tensorWordDenAll wR8fR820pG : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR820pH_check : wR8fR820pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR820pD_ok : wR8fR820pHD.ok = true ∧ wR8fR820pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR820pHD_cols : ∀ i : Fin 24, qmWordP (wR8fR820pHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR820pHD.colsP i.val, wR8fR820pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR820pHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR820pHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR820pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR820pHT_check : shortCheckF wR8fR820pHD srcRootEightCShort.flat wR8fR820pHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR820pT_labels : wR8fR820pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR820pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR820pH_growth : tensorWordGrowthAll wR8fR820pH * 15 = 3840 := by decide

/-- The word bound of the target word. -/
theorem wR8fR820pG_growth : tensorWordGrowthAll wR8fR820pG * 56 = 29360128 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR820pL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR820pH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR820pL.real := by
  have hT := (tensorWordAll_actual wR8fR820pH (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wR8fR820pH_growth]; norm_num) 32).2
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR820pHW wR8fR820pH_check wR8fR820pHD
      wR8fR820pD_ok.1 wR8fR820pHD_cols
    wR8fR820pHD_rows wR8fR820pHT wR8fR820pHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
