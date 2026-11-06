/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c3pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFast

/-! # Factory checks (definitions, source side) of the identification Sixth[6]+ <-> Tenth[81]-
(record gforest:S6c3+, e = 1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWGoctadXGforestS6c3pChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wGoctadXGforestS6c3pH : List IdentLetter := wGoctadXGforestS6c3pHW.map Prod.fst

/-- The target word. -/
def wGoctadXGforestS6c3pG : List IdentLetter := wGoctadXGforestS6c3pGW.map Prod.fst

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadXGforestS6c3pH`. -/
def wGoctadXGforestS6c3pHPlan : List TPlan :=
  [.letter (.xi),
    .run
      [(1, true)]
      [.trans 2 3, .trans 2 7, .trans 9 2, .trans 9 5, .trans 3 10, .trans 8 1, .trans 1 4,
        .trans 1 8, .trans 8 1, .trans 1 6, .trans 8 5, .trans 8 0, .trans 0 6,
        .trans 0 9, .trans 1 9, .trans 9 0, .trans 5 6, .trans 6 5, .trans 0 9,
        .trans 9 2, .trans 2 3, .trans 2 7, .trans 5 6],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (0, true), (0, true)]
      [.trans 2 3, .trans 8 2, .trans 10 2, .trans 10 0, .trans 7 10, .trans 3 8, .trans 0 7,
        .trans 7 6, .trans 5 0, .trans 7 9, .trans 6 2, .trans 5 6, .trans 6 5,
        .trans 5 6, .trans 0 1, .trans 5 10, .trans 10 11, .trans 10 4, .trans 4 8,
        .trans 6 3, .trans 7 4, .trans 6 4, .trans 4 7, .trans 2 9, .trans 7 4,
        .trans 1 9, .trans 9 8, .trans 8 11, .trans 2 3, .trans 8 3]]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadXGforestS6c3pHPlan_word : planWord wGoctadXGforestS6c3pHPlan =
    wGoctadXGforestS6c3pH := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadXGforestS6c3pHPlan_ok : planOk wGoctadXGforestS6c3pHPlan = true := by decide +kernel

/-- Tensor plan (fused monomial runs, gtenth) of the word `wGoctadXGforestS6c3pG`. -/
def wGoctadXGforestS6c3pGPlan : List TPlan :=
  [.letter (.qel (qmElt (5735976, false))),
    .letter (.sign 352 0),
    .run
      [(0, false), (1, false), (0, true), (1, false), (0, false), (1, false), (0, false),
        (0, false), (0, false), (1, false), (0, true), (1, false), (0, false),
        (1, false), (0, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, false), (0, false), (0, false), (0, false),
        (0, false), (1, true), (0, true), (0, true), (1, true), (0, false), (0, false),
        (0, false), (1, true), (0, true), (0, true), (0, true), (1, true), (0, true),
        (0, true), (0, true), (1, true), (0, false), (0, false), (1, true), (0, false),
        (1, true), (0, true), (1, false), (0, false), (0, false), (1, false), (0, false),
        (0, false), (1, false), (0, true), (0, true), (1, false), (0, false), (1, false),
        (0, true), (0, true), (0, true), (1, false), (0, true), (0, true), (1, false),
        (0, false)]
      [.trans 1 0, .trans 0 1, .trans 0 2, .trans 0 3, .trans 0 9, .trans 0 10, .trans 4 1,
        .trans 1 4, .trans 1 6, .trans 1 9, .trans 1 10, .trans 2 0, .trans 2 3,
        .trans 2 9, .trans 2 10, .trans 5 3, .trans 3 1, .trans 3 5, .trans 3 7,
        .trans 4 0, .trans 4 3, .trans 7 5, .trans 5 0, .trans 5 1, .trans 5 2,
        .trans 5 3, .trans 5 7, .trans 9 6, .trans 6 2, .trans 6 3, .trans 6 5,
        .trans 6 9, .trans 6 10, .trans 7 2, .trans 7 3, .trans 7 6, .trans 7 9,
        .trans 7 10, .trans 8 0, .trans 8 2, .trans 8 5, .trans 10 9, .trans 9 5,
        .trans 9 6, .trans 9 8, .trans 9 10, .trans 10 0, .trans 10 1, .trans 10 2,
        .trans 10 3, .trans 10 6, .trans 10 8, .trans 10 9],
    .letter (.xi),
    .letter (.xi),
    .run
      [(0, true), (0, true), (1, true)]
      [.trans 5 4, .trans 7 1, .trans 8 3, .trans 3 5, .trans 9 10, .trans 6 7, .trans 1 9,
        .trans 9 0, .trans 10 8, .trans 8 6, .trans 6 2, .trans 7 4, .trans 5 11,
        .trans 7 11, .trans 9 11, .trans 0 4, .trans 4 9, .trans 9 3, .trans 9 2,
        .trans 9 1, .trans 2 7, .trans 9 11, .trans 5 7, .trans 1 7, .trans 7 2,
        .trans 7 10, .trans 0 3, .trans 3 8, .trans 3 10, .trans 8 3, .trans 8 6,
        .trans 6 8, .trans 6 5, .trans 5 0, .trans 0 4, .trans 4 2, .trans 2 6,
        .trans 2 8, .trans 8 10, .trans 10 1, .trans 1 6, .trans 6 5, .trans 1 3],
    .letter (.xi),
    .run
      [(0, true), (1, true)]
      [.trans 1 0, .trans 0 1, .trans 0 2, .trans 0 3, .trans 0 5, .trans 0 7, .trans 0 9,
        .trans 0 10, .trans 0 11, .trans 5 1, .trans 1 0, .trans 1 5, .trans 1 7,
        .trans 1 8, .trans 1 10, .trans 1 11, .trans 2 3, .trans 2 4, .trans 2 5,
        .trans 2 11, .trans 4 3, .trans 3 0, .trans 3 2, .trans 3 4, .trans 3 6,
        .trans 3 9, .trans 3 10, .trans 3 11, .trans 9 4, .trans 4 0, .trans 4 9,
        .trans 4 10, .trans 4 11, .trans 6 5, .trans 5 1, .trans 5 3, .trans 5 4,
        .trans 5 6, .trans 5 8, .trans 8 6, .trans 6 0, .trans 6 1, .trans 6 2,
        .trans 6 3, .trans 6 8, .trans 6 10, .trans 6 11, .trans 7 0, .trans 7 1,
        .trans 7 3, .trans 7 4, .trans 7 10, .trans 7 11, .trans 8 0, .trans 8 1,
        .trans 8 2, .trans 8 4, .trans 8 6, .trans 8 10, .trans 9 3, .trans 9 4,
        .trans 9 5, .trans 9 6, .trans 9 8, .trans 9 10, .trans 9 11, .trans 10 1,
        .trans 10 4, .trans 10 6],
    .letter (.sign 32 0),
    .run
      [(0, true)]
      [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
        .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6,
        .trans 4 5, .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2,
        .trans 10 1, .trans 9 11, .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0,
        .trans 8 3, .trans 0 10, .trans 0 11],
    .letter (.xi),
    .letter (.xi)]

set_option maxRecDepth 100000 in
/-- The plan expands to the word. -/
theorem wGoctadXGforestS6c3pGPlan_word : planWord wGoctadXGforestS6c3pGPlan =
    wGoctadXGforestS6c3pG := by
  rfl

set_option maxRecDepth 100000 in
/-- The plan is admissible. -/
theorem wGoctadXGforestS6c3pGPlan_ok : planOk wGoctadXGforestS6c3pGPlan = true := by decide +kernel

/-- The packed tensor of the source image. -/
def wGoctadXGforestS6c3pHX : List SVec := tensorPlanF 64 wGoctadXGforestS6c3pHPlan (sixthSXF 64)

/-- The packed tensor of the target image. -/
def wGoctadXGforestS6c3pGX : List SVec := tensorPlanF 64 wGoctadXGforestS6c3pGPlan (tenthSrcXL 64)

/-- The representation of the source image. -/
def wGoctadXGforestS6c3pL : IdentVec :=
  ⟨sixthSrcMat.act identSpatialAlphabet wGoctadXGforestS6c3pH, ShortData.ofList
      wGoctadXGforestS6c3pHT, 1 / 32,
    tensorRat 64 wGoctadXGforestS6c3pHX ((tensorWordDenAll wGoctadXGforestS6c3pH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wGoctadXGforestS6c3pW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet wGoctadXGforestS6c3pG, ShortData.ofList
      wGoctadXGforestS6c3pGT, (1 / 128),
    tensorRat 64 wGoctadXGforestS6c3pGX ((tensorWordDenAll wGoctadXGforestS6c3pG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wGoctadXGforestS6c3pH_check : wGoctadXGforestS6c3pHW.all (fun p => identLetterCheckP p.1
    p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wGoctadXGforestS6c3pD_ok : wGoctadXGforestS6c3pHD.ok = true ∧ wGoctadXGforestS6c3pGD.ok =
    true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wGoctadXGforestS6c3pHD_cols : ∀ i : Fin 24, qmWordP (wGoctadXGforestS6c3pHW.map Prod.snd)
    (2 ^ i.val, false) =
    (fld 24 wGoctadXGforestS6c3pHD.colsP i.val, wGoctadXGforestS6c3pHD.coeff.testBit i.val) := by
        decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wGoctadXGforestS6c3pHD_rows : ∀ i : Fin 24,
    fld 24 wGoctadXGforestS6c3pHD.rowsP i.val = rowsOf (fun j => fld 24
        wGoctadXGforestS6c3pHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wGoctadXGforestS6c3pHT_check : shortCheckF wGoctadXGforestS6c3pHD sixthLitShort.flat
    wGoctadXGforestS6c3pHT = true :=
  shortCheckPk_sound _ 10 30 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wGoctadXGforestS6c3pT_labels : wGoctadXGforestS6c3pHT.all (fun p => decide (p.1 < 98280))
    = true ∧
    wGoctadXGforestS6c3pGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wGoctadXGforestS6c3pH_growth : tensorWordGrowthAll wGoctadXGforestS6c3pH * (2 ^ 8 - 1) =
    4278190080 := by decide

/-- The word bound of the target word. -/
theorem wGoctadXGforestS6c3pG_growth : tensorWordGrowthAll wGoctadXGforestS6c3pG * 15 =
    1055531162664960 := by decide

/-- The coordinates of the source image. -/
theorem wGoctadXGforestS6c3pL_actual : griessConwayEncode (rhoLocal (identWordLocal
    wGoctadXGforestS6c3pH)
    (generatedAxisGlobalTwelveRepresentative 5)) = wGoctadXGforestS6c3pL.real := by
  have hT := (tensorPlanF_actual wGoctadXGforestS6c3pHPlan wGoctadXGforestS6c3pHPlan_ok
      (sixthSXF_bndF (w := 64) (by norm_num))
    (by rw [wGoctadXGforestS6c3pHPlan_word, wGoctadXGforestS6c3pH_growth]; norm_num) 32).2
  rw [wGoctadXGforestS6c3pHPlan_word] at hT
  exact IdentVec.word_actual (sixthSrcVecF 64) wGoctadXGforestS6c3pHW wGoctadXGforestS6c3pH_check
      wGoctadXGforestS6c3pHD wGoctadXGforestS6c3pD_ok.1 wGoctadXGforestS6c3pHD_cols
    wGoctadXGforestS6c3pHD_rows wGoctadXGforestS6c3pHT wGoctadXGforestS6c3pHT_check _ hT _
        (sixthSrcF_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
