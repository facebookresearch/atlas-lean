/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPack
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortWordP
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF

/-! # Factory checks (definitions, source side) of the identification Root8[25]- <-> Root8[25]-
(record r8f:R820-, e = -1)

The two representations are computed from the source vectors (matrix block by the spatial
alphabet, short block by a checked transport onto the literal target lists, tensor block by
packed words); the source image is bound to its genuine coordinates here, the target image in
`GeneratedAxisGlobalIdentWR8fR820nChecks`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word. -/
def wR8fR820nH : List IdentLetter := wR8fR820nHW.map Prod.fst

/-- The target word. -/
def wR8fR820nG : List IdentLetter := wR8fR820nGW.map Prod.fst

/-- The packed tensor of the source image. -/
def wR8fR820nHX : List SVec := tensorWordAll 64 wR8fR820nH (rootEightSrcXL 64)

/-- The packed tensor of the target image. -/
def wR8fR820nGX : List SVec := tensorWordAll 64 wR8fR820nG (rootEightSrcXL 64)

/-- The representation of the source image. -/
def wR8fR820nL : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR820nH, ShortData.ofList wR8fR820nHT, (1 / 128),
    tensorRat 64 wR8fR820nHX ((tensorWordDenAll wR8fR820nH : ℚ) * 32)⟩

/-- The representation of the target image. -/
def wR8fR820nW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet wR8fR820nG, ShortData.ofList wR8fR820nGT, (1 / 128),
    tensorRat 64 wR8fR820nGX ((tensorWordDenAll wR8fR820nG : ℚ) * 32)⟩

set_option maxRecDepth 100000 in
/-- The letter data of the source word are certified. -/
theorem wR8fR820nH_check : wR8fR820nHW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem wR8fR820nD_ok : wR8fR820nHD.ok = true ∧ wR8fR820nGD.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the source word evaluate the word on the generators. -/
theorem wR8fR820nHD_cols : ∀ i : Fin 24, qmWordP (wR8fR820nHW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR820nHD.colsP i.val, wR8fR820nHD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the source word. -/
theorem wR8fR820nHD_rows : ∀ i : Fin 24,
    fld 24 wR8fR820nHD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR820nHD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source image is transported onto the literal targets. -/
theorem wR8fR820nHT_check : shortCheckF wR8fR820nHD srcRootEightCShort.flat wR8fR820nHT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem wR8fR820nT_labels : wR8fR820nHT.all (fun p => decide (p.1 < 98280)) = true ∧
    wR8fR820nGT.all (fun p => decide (p.1 < 98280)) = true := by decide +kernel

/-- The word bound of the source word. -/
theorem wR8fR820nH_growth : tensorWordGrowthAll wR8fR820nH * 15 = 3840 := by decide

/-- The word bound of the target word. -/
theorem wR8fR820nG_growth : tensorWordGrowthAll wR8fR820nG * 15 = 30720 := by decide

/-- The coordinates of the source image. -/
theorem wR8fR820nL_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR820nH)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR820nL.real := by
  have hT := (tensorWordAll_actual wR8fR820nH (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wR8fR820nH_growth]; norm_num) 32).2
  exact IdentVec.word_actual (rootEightSrcVecL 64) wR8fR820nHW wR8fR820nH_check wR8fR820nHD
      wR8fR820nD_ok.1 wR8fR820nHD_cols
    wR8fR820nHD_rows wR8fR820nHT wR8fR820nHT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
