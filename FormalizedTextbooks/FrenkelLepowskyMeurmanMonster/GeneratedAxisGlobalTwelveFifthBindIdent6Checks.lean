/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindIdent6Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindTriangle
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord

/-! # Data checks of the Fifth self identification (I6s+) at the root 6 representative

With `h₆ = xi⁻¹ P₁⁻¹ P₀⁻¹` (`generatedAxisGlobalTwelveFifthBindCosetLetters 2`) and
`g = generatedAxisGlobalTwelveFifthBindPrefix6p ++ h₆`, the identification
`GeneratedAxisGlobalTwelveFifthBindIdent6p` claims `sExtra (h₆ v₅) = g v₅`. Both sides are local
images of the Fifth axis: their representations are computed from `fifthSrcVecW 64` (matrix by the
spatial alphabet, short block by a checked transport onto the literal target lists of
`GeneratedAxisGlobalTwelveFifthBindIdent6Data`, tensor block by packed words), exactly as in
gident's pilot `GeneratedAxisGlobalIdentPilot1Checks`. This module certifies the literal short data
and binds both representations to the genuine coordinates. The identification itself (the pairing
value `128`) is not asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word `h₆`. -/
def generatedAxisGlobalTwelveFifthBind6pH : List IdentLetter :=
  generatedAxisGlobalTwelveFifthBind6pWh.map Prod.fst

/-- The destination word `g`. -/
def generatedAxisGlobalTwelveFifthBind6pG : List IdentLetter :=
  generatedAxisGlobalTwelveFifthBind6pWg.map Prod.fst

/-- The source word is the root 6 representative word. -/
theorem generatedAxisGlobalTwelveFifthBind6pH_eq :
    generatedAxisGlobalTwelveFifthBind6pH = generatedAxisGlobalTwelveFifthBindCosetLetters 2 :=
  rfl

/-- The destination word is the phase-fixing prefix followed by the representative word. -/
theorem generatedAxisGlobalTwelveFifthBind6pG_eq :
    generatedAxisGlobalTwelveFifthBind6pG =
      generatedAxisGlobalTwelveFifthBindPrefix6p ++
        generatedAxisGlobalTwelveFifthBindCosetLetters 2 :=
  rfl

/-- The packed tensor of `h₆ v₅`. -/
def generatedAxisGlobalTwelveFifthBind6pLX : List SVec :=
  tensorWordAll 64 generatedAxisGlobalTwelveFifthBind6pH (fifthSrcXW 64)

/-- The packed tensor of `g v₅`. -/
def generatedAxisGlobalTwelveFifthBind6pWX : List SVec :=
  tensorWordAll 64 generatedAxisGlobalTwelveFifthBind6pG (fifthSrcXW 64)

/-- The representation of `h₆ v₅`. -/
def generatedAxisGlobalTwelveFifthBind6pL : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet generatedAxisGlobalTwelveFifthBind6pH,
    ShortData.ofList generatedAxisGlobalTwelveFifthBind6pTh, 1 / 16,
    tensorRat 64 generatedAxisGlobalTwelveFifthBind6pLX
      ((tensorWordDenAll generatedAxisGlobalTwelveFifthBind6pH : ℚ) * 1)⟩

/-- The representation of `g v₅`. -/
def generatedAxisGlobalTwelveFifthBind6pW : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet generatedAxisGlobalTwelveFifthBind6pG,
    ShortData.ofList generatedAxisGlobalTwelveFifthBind6pTg, 1 / 16,
    tensorRat 64 generatedAxisGlobalTwelveFifthBind6pWX
      ((tensorWordDenAll generatedAxisGlobalTwelveFifthBind6pG : ℚ) * 1)⟩

/-! ## Checks of the literal short data -/

set_option maxRecDepth 100000 in
/-- The letter data of `h₆` are certified. -/
theorem generatedAxisGlobalTwelveFifthBind6pWh_check :
    generatedAxisGlobalTwelveFifthBind6pWh.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of `g` are certified. -/
theorem generatedAxisGlobalTwelveFifthBind6pWg_check :
    generatedAxisGlobalTwelveFifthBind6pWg.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem generatedAxisGlobalTwelveFifthBind6pD_ok :
    generatedAxisGlobalTwelveFifthBind6pDh.ok = true ∧
      generatedAxisGlobalTwelveFifthBind6pDg.ok = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `h₆` evaluate the word on the generators. -/
theorem generatedAxisGlobalTwelveFifthBind6pDh_cols : ∀ i : Fin 24,
    qmWordP (generatedAxisGlobalTwelveFifthBind6pWh.map Prod.snd) (2 ^ i.val, false) =
      (fld 24 generatedAxisGlobalTwelveFifthBind6pDh.colsP i.val,
        generatedAxisGlobalTwelveFifthBind6pDh.coeff.testBit i.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `g` evaluate the word on the generators. -/
theorem generatedAxisGlobalTwelveFifthBind6pDg_cols : ∀ i : Fin 24,
    qmWordP (generatedAxisGlobalTwelveFifthBind6pWg.map Prod.snd) (2 ^ i.val, false) =
      (fld 24 generatedAxisGlobalTwelveFifthBind6pDg.colsP i.val,
        generatedAxisGlobalTwelveFifthBind6pDg.coeff.testBit i.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `h₆`. -/
theorem generatedAxisGlobalTwelveFifthBind6pDh_rows : ∀ i : Fin 24,
    fld 24 generatedAxisGlobalTwelveFifthBind6pDh.rowsP i.val =
      rowsOf (fun j => fld 24 generatedAxisGlobalTwelveFifthBind6pDh.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `g`. -/
theorem generatedAxisGlobalTwelveFifthBind6pDg_rows : ∀ i : Fin 24,
    fld 24 generatedAxisGlobalTwelveFifthBind6pDg.rowsP i.val =
      rowsOf (fun j => fld 24 generatedAxisGlobalTwelveFifthBind6pDg.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `h₆ v₅` is transported onto the literal targets. -/
theorem generatedAxisGlobalTwelveFifthBind6pTh_check :
    shortCheckF generatedAxisGlobalTwelveFifthBind6pDh fifthSrcShort.flat
      generatedAxisGlobalTwelveFifthBind6pTh = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `g v₅` is transported onto the literal targets. -/
theorem generatedAxisGlobalTwelveFifthBind6pTg_check :
    shortCheckF generatedAxisGlobalTwelveFifthBind6pDg fifthSrcShort.flat
      generatedAxisGlobalTwelveFifthBind6pTg = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem generatedAxisGlobalTwelveFifthBind6pT_labels :
    generatedAxisGlobalTwelveFifthBind6pTh.all (fun p => decide (p.1 < 98280)) = true ∧
      generatedAxisGlobalTwelveFifthBind6pTg.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-! ## The two local images -/

/-- The word bound of `h₆`. -/
theorem generatedAxisGlobalTwelveFifthBind6pH_growth :
    tensorWordGrowthAll generatedAxisGlobalTwelveFifthBind6pH * 64 = 4194304 := by decide

/-- The word bound of `g`. -/
theorem generatedAxisGlobalTwelveFifthBind6pG_growth :
    tensorWordGrowthAll generatedAxisGlobalTwelveFifthBind6pG * 64 = 33554432 := by decide

/-- The coordinates of `h₆ v₅`. -/
theorem generatedAxisGlobalTwelveFifthBind6pL_actual :
    griessConwayEncode (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBind6pH)
      (generatedAxisGlobalTwelveRepresentative 4)) = generatedAxisGlobalTwelveFifthBind6pL.real :=
  IdentVec.word_actual (fifthSrcVecW 64) generatedAxisGlobalTwelveFifthBind6pWh
    generatedAxisGlobalTwelveFifthBind6pWh_check generatedAxisGlobalTwelveFifthBind6pDh
    generatedAxisGlobalTwelveFifthBind6pD_ok.1 generatedAxisGlobalTwelveFifthBind6pDh_cols
    generatedAxisGlobalTwelveFifthBind6pDh_rows generatedAxisGlobalTwelveFifthBind6pTh
    generatedAxisGlobalTwelveFifthBind6pTh_check _
    (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind6pH (fifthSrcXW_bnd (by norm_num))
      (by rw [generatedAxisGlobalTwelveFifthBind6pH_growth]; norm_num) 1).2 _
    (fifthSrcW_rep (by norm_num))

/-- The coordinates of `g v₅`. -/
theorem generatedAxisGlobalTwelveFifthBind6pW_actual :
    griessConwayEncode (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBind6pG)
      (generatedAxisGlobalTwelveRepresentative 4)) = generatedAxisGlobalTwelveFifthBind6pW.real :=
  IdentVec.word_actual (fifthSrcVecW 64) generatedAxisGlobalTwelveFifthBind6pWg
    generatedAxisGlobalTwelveFifthBind6pWg_check generatedAxisGlobalTwelveFifthBind6pDg
    generatedAxisGlobalTwelveFifthBind6pD_ok.2 generatedAxisGlobalTwelveFifthBind6pDg_cols
    generatedAxisGlobalTwelveFifthBind6pDg_rows generatedAxisGlobalTwelveFifthBind6pTg
    generatedAxisGlobalTwelveFifthBind6pTg_check _
    (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind6pG (fifthSrcXW_bnd (by norm_num))
      (by rw [generatedAxisGlobalTwelveFifthBind6pG_growth]; norm_num) 1).2 _
    (fifthSrcW_rep (by norm_num))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
