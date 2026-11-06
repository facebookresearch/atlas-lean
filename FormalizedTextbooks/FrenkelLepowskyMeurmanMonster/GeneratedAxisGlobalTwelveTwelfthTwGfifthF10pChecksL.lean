/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGfifthF10pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Fifth[10]+ <-> Twelfth[36]-
(record gfifth:F10+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalTwelveTwelfthTwGfifthF10pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def twGfifthF10pH : List IdentLetter := twGfifthF10pHW.map Prod.fst

/-- The target word. -/
def twGfifthF10pG : List IdentLetter := twGfifthF10pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `twGfifthF10pH`. -/
def twGfifthF10pHPlan : List TPlan :=
  [.letter (.sign 2048 0),
    .letter (.xi),
    .letter (.sign 3072 0),
    .run
      [(1, true), (0, true), (1, true), (0, false), (0, false), (1, true), (0, true),
        (1, true), (0, false), (0, false), (0, false), (1, true), (0, true), (0, true),
        (1, true), (0, false), (1, true), (0, false), (0, false), (1, true)]
      [.trans 3 1, .trans 10 3, .trans 5 4, .trans 11 10, .trans 2 6, .trans 9 10, .trans 8 3,
        .trans 7 0, .trans 7 2, .trans 0 6, .trans 4 0, .trans 2 11, .trans 3 2,
        .trans 4 5, .trans 6 11, .trans 11 3, .trans 6 0, .trans 1 0, .trans 10 3,
        .trans 3 7, .trans 7 5, .trans 6 5, .trans 5 11, .trans 11 10, .trans 10 5,
        .trans 10 8, .trans 10 11, .trans 8 9, .trans 9 7, .trans 8 0, .trans 0 1,
        .trans 1 6, .trans 2 4, .trans 6 4, .trans 4 6, .trans 4 7, .trans 6 2,
        .trans 6 5],
    .letter (.xi),
    .letter (.sign 3584 0),
    .run
      [(0, false), (1, true), (0, false), (0, false), (1, true), (0, true), (1, true),
        (0, false), (0, false), (1, true), (0, false), (0, false), (0, false), (1, true),
        (0, false), (1, true), (0, true), (1, true), (0, true)]
      [.trans 4 3, .trans 4 5, .trans 7 4, .trans 4 1, .trans 5 11, .trans 1 8, .trans 10 7,
        .trans 5 10, .trans 6 2, .trans 9 10, .trans 8 11, .trans 7 6, .trans 2 6,
        .trans 8 4, .trans 6 5, .trans 10 7, .trans 6 2, .trans 10 9, .trans 2 11,
        .trans 5 3, .trans 0 3, .trans 3 0, .trans 0 8, .trans 9 5, .trans 2 7,
        .trans 2 1, .trans 10 1, .trans 1 11, .trans 1 4, .trans 8 5, .trans 1 3,
        .trans 8 0, .trans 5 4],
    .letter (.xi),
    .letter (.sign 1024 0),
    .run
      [(0, true), (0, true), (1, true), (0, true), (0, true), (0, true), (1, true), (0, true),
        (0, true), (1, true), (0, false), (1, true), (0, true), (0, true), (0, true),
        (1, true), (0, false), (1, true), (0, true)]
      [.trans 0 2, .trans 0 4, .trans 0 6, .trans 0 7, .trans 0 9, .trans 0 10, .trans 0 11,
        .trans 2 1, .trans 1 2, .trans 1 3, .trans 1 7, .trans 1 9, .trans 1 10,
        .trans 1 11, .trans 3 2, .trans 2 0, .trans 2 3, .trans 2 4, .trans 2 7,
        .trans 2 8, .trans 2 10, .trans 4 3, .trans 3 2, .trans 3 4, .trans 3 9,
        .trans 6 4, .trans 4 1, .trans 4 2, .trans 4 6, .trans 4 9, .trans 5 2,
        .trans 5 3, .trans 5 9, .trans 7 6, .trans 6 2, .trans 6 3, .trans 6 4,
        .trans 6 5, .trans 6 7, .trans 6 9, .trans 6 10, .trans 6 11, .trans 9 7,
        .trans 7 0, .trans 7 1, .trans 7 3, .trans 7 9, .trans 9 8, .trans 8 2,
        .trans 8 3, .trans 8 4, .trans 8 6, .trans 8 9, .trans 8 10, .trans 8 11,
        .trans 9 0, .trans 9 3, .trans 9 5, .trans 9 7, .trans 9 11, .trans 10 0,
        .trans 10 2, .trans 10 6, .trans 10 8, .trans 10 9, .trans 10 11],
    .letter (.xi),
    .run
      [(0, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false),
        (1, true), (0, true), (0, true)]
      [.trans 0 3, .trans 1 0, .trans 4 10, .trans 6 7, .trans 5 9, .trans 9 6, .trans 5 4,
        .trans 1 8, .trans 8 5, .trans 11 8, .trans 9 1, .trans 3 7, .trans 3 11,
        .trans 4 2, .trans 0 2, .trans 2 11, .trans 11 8, .trans 10 9, .trans 9 4,
        .trans 4 1, .trans 1 7, .trans 7 8, .trans 5 6, .trans 6 1, .trans 8 5,
        .trans 1 3, .trans 7 10, .trans 1 6, .trans 8 6, .trans 3 0, .trans 6 9,
        .trans 3 9, .trans 3 10, .trans 5 0, .trans 0 5, .trans 2 0, .trans 2 5,
        .trans 5 2],
    .letter (.xi),
    .run
      [(0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, true),
        (0, true), (1, true), (0, false), (1, true), (0, true), (0, true), (1, true),
        (0, false), (1, true), (0, false), (1, true), (0, true), (1, true)]
      [.trans 4 11, .trans 6 8, .trans 6 2, .trans 7 3, .trans 9 2, .trans 2 3, .trans 3 4,
        .trans 9 1, .trans 9 5, .trans 9 7, .trans 7 10, .trans 4 0, .trans 5 8,
        .trans 1 6, .trans 6 0, .trans 0 11, .trans 10 7, .trans 10 6, .trans 8 2,
        .trans 2 1, .trans 2 6, .trans 0 1, .trans 1 3, .trans 3 6, .trans 4 7,
        .trans 5 3, .trans 5 6, .trans 6 3, .trans 6 4, .trans 6 5, .trans 6 7,
        .trans 7 8, .trans 9 8, .trans 8 9, .trans 9 0, .trans 9 1, .trans 9 4,
        .trans 9 5, .trans 9 6, .trans 9 7]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem twGfifthF10pHPlan_word : planWord twGfifthF10pHPlan = twGfifthF10pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem twGfifthF10pHPlan_ok : planOk twGfifthF10pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `twGfifthF10pG`. -/
def twGfifthF10pGPlan : List TPlan :=
  [.letter (.qel (qmElt (6962987, true))),
    .letter (.sign 1992 0),
    .run
      [(0, false), (1, false), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, true), (0, true), (1, false), (0, false), (1, false), (0, true), (0, true),
        (0, true), (1, false), (0, true), (0, true), (0, true), (1, false), (0, false),
        (1, false), (0, true), (1, false), (0, false)]
      [.trans 1 0, .trans 0 1, .trans 0 3, .trans 0 4, .trans 0 5, .trans 0 7, .trans 0 8,
        .trans 1 0, .trans 1 3, .trans 1 4, .trans 1 5, .trans 1 8, .trans 1 11,
        .trans 4 2, .trans 2 0, .trans 2 1, .trans 2 4, .trans 2 5, .trans 2 7,
        .trans 2 8, .trans 7 3, .trans 3 0, .trans 3 1, .trans 3 7, .trans 7 4,
        .trans 4 0, .trans 4 1, .trans 4 2, .trans 4 7, .trans 4 11, .trans 5 8,
        .trans 5 9, .trans 6 0, .trans 6 1, .trans 6 2, .trans 6 4, .trans 6 5,
        .trans 6 8, .trans 6 10, .trans 6 11, .trans 8 7, .trans 7 2, .trans 7 3,
        .trans 7 8, .trans 10 8, .trans 8 0, .trans 8 1, .trans 8 3, .trans 8 4,
        .trans 8 5, .trans 8 10, .trans 8 11, .trans 9 2, .trans 9 4, .trans 9 10,
        .trans 10 2, .trans 10 3, .trans 10 5, .trans 10 6, .trans 10 7, .trans 10 8],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, false), (1, true), (0, true), (0, true), (1, true), (0, false), (0, false)]
      [.trans 10 11, .trans 1 10, .trans 3 5, .trans 2 1, .trans 1 6, .trans 4 3, .trans 7 2,
        .trans 6 4, .trans 8 0, .trans 0 1, .trans 2 8, .trans 10 2, .trans 1 4,
        .trans 4 2, .trans 2 3, .trans 10 8, .trans 8 1, .trans 1 10, .trans 8 7,
        .trans 5 7, .trans 7 3, .trans 10 6, .trans 3 0, .trans 0 8, .trans 6 11,
        .trans 10 9, .trans 0 3, .trans 4 0, .trans 0 4, .trans 7 6, .trans 7 11,
        .trans 1 0, .trans 3 0, .trans 3 1, .trans 3 5, .trans 3 8, .trans 6 9,
        .trans 8 6, .trans 8 9, .trans 9 0, .trans 9 1, .trans 9 3, .trans 9 5,
        .trans 9 6, .trans 9 8]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem twGfifthF10pGPlan_word : planWord twGfifthF10pGPlan = twGfifthF10pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem twGfifthF10pGPlan_ok : planOk twGfifthF10pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def twGfifthF10pHX : List SVec := tensorPlanF 112 twGfifthF10pHPlan (fifthSrcXW 112)

/-- The packed tensor of the target image. -/
def twGfifthF10pGX : List SVec := tensorPlanF 112 twGfifthF10pGPlan (twelfthSrcXW 112)

/-- The representation of the source image. -/
def twGfifthF10pL : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet twGfifthF10pH, ShortData.ofList twGfifthF10pHT, 1 / 16,
    tensorRat 112 twGfifthF10pHX ((tensorWordDenAll twGfifthF10pH : ℚ) * 1)⟩

/-- The representation of the target image. -/
def twGfifthF10pW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet twGfifthF10pG, ShortData.ofList twGfifthF10pGT, (1 / 128),
    tensorRat 112 twGfifthF10pGX ((tensorWordDenAll twGfifthF10pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem twGfifthF10pH_check : twGfifthF10pHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem twGfifthF10pD_ok : twGfifthF10pHD.ok = true ∧ twGfifthF10pGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem twGfifthF10pHD_cols : ∀ i : Fin 24, qmWordP (twGfifthF10pHW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 twGfifthF10pHD.colsP i.val, twGfifthF10pHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem twGfifthF10pHD_rows : ∀ i : Fin 24,
    fld 24 twGfifthF10pHD.rowsP i.val = rowsOf (fun j => fld 24 twGfifthF10pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem twGfifthF10pHT_check : shortCheckF twGfifthF10pHD fifthSrcShort.flat twGfifthF10pHT = true
    :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem twGfifthF10pT_labels : twGfifthF10pHT.all (fun p => decide (p.1 < 98280)) = true ∧
    twGfifthF10pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem twGfifthF10pH_growth : tensorWordGrowthAll twGfifthF10pH * 64 = 288230376151711744 := by
    decide

/-- The word bound of the target word. -/
theorem twGfifthF10pG_growth : tensorWordGrowthAll twGfifthF10pG * 15 = 7864320 := by decide

/-- The coordinates of the source image. -/
theorem twGfifthF10pL_actual : griessConwayEncode (rhoLocal (identWordLocal twGfifthF10pH)
    (generatedAxisGlobalTwelveRepresentative 4)) = twGfifthF10pL.real := by
  have hT := (tensorPlanF_actual twGfifthF10pHPlan twGfifthF10pHPlan_ok (fifthSrcXW_bnd (w := 112)
      (by norm_num))
    (by rw [twGfifthF10pHPlan_word, twGfifthF10pH_growth]; norm_num) 1).2
  rw [twGfifthF10pHPlan_word] at hT
  exact IdentVec.word_actual (fifthSrcVecW 112) twGfifthF10pHW twGfifthF10pH_check twGfifthF10pHD
      twGfifthF10pD_ok.1 twGfifthF10pHD_cols
    twGfifthF10pHD_rows twGfifthF10pHT twGfifthF10pHT_check _ hT _ (fifthSrcW_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
