/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindIdent12Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindTriangle
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW

/-! # Data checks of the Fifth identification (I12-) at the root 12 representative

The source is the local image `h₁₂ v₅` of the Fifth axis with
`h₁₂ = generatedAxisGlobalTwelveFifthBindCosetLetters 3`, the target is the local image `g v₄` of
the Fourth axis (worker grecip's `fourthSrcVecW`), as in gident's pilot
`GeneratedAxisGlobalIdentPilot1Checks` and grecip's
`GeneratedAxisGlobalTwelveFourthIdentF2Checks`. This module
certifies the literal data and binds both representations to the genuine coordinates. The
identification itself is not asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word `h₁₂`. -/
def generatedAxisGlobalTwelveFifthBind12H : List IdentLetter :=
  generatedAxisGlobalTwelveFifthBind12pWh.map Prod.fst

/-- The source word is the root 12 representative word. -/
theorem generatedAxisGlobalTwelveFifthBind12H_eq :
    generatedAxisGlobalTwelveFifthBind12H = generatedAxisGlobalTwelveFifthBindCosetLetters 3 :=
  rfl

/-- The destination word `g`. -/
def generatedAxisGlobalTwelveFifthBind12mG : List IdentLetter :=
  generatedAxisGlobalTwelveFifthBind12mWg.map Prod.fst

/-- The packed tensor of `h₁₂ v₅`. -/
def generatedAxisGlobalTwelveFifthBind12LX : List SVec :=
  tensorWordAll 64 generatedAxisGlobalTwelveFifthBind12H (fifthSrcXW 64)

/-- The packed tensor of `g v₄`. -/
def generatedAxisGlobalTwelveFifthBind12mWX : List SVec :=
  tensorWordAll 64 generatedAxisGlobalTwelveFifthBind12mG (fourthSrcXW 64)

/-- The representation of `h₁₂ v₅`. -/
def generatedAxisGlobalTwelveFifthBind12L : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet generatedAxisGlobalTwelveFifthBind12H,
    ShortData.ofList generatedAxisGlobalTwelveFifthBind12pTh, 1 / 16,
    tensorRat 64 generatedAxisGlobalTwelveFifthBind12LX
      ((tensorWordDenAll generatedAxisGlobalTwelveFifthBind12H : ℚ) * 1)⟩

/-- The representation of `g v₄`. -/
def generatedAxisGlobalTwelveFifthBind12mW : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet generatedAxisGlobalTwelveFifthBind12mG,
    ShortData.ofList generatedAxisGlobalTwelveFifthBind12mTg, 1 / 8,
    tensorRat 64 generatedAxisGlobalTwelveFifthBind12mWX
      ((tensorWordDenAll generatedAxisGlobalTwelveFifthBind12mG : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of `h₁₂` are certified. -/
theorem generatedAxisGlobalTwelveFifthBind12Wh_check :
    generatedAxisGlobalTwelveFifthBind12pWh.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of `g` are certified. -/
theorem generatedAxisGlobalTwelveFifthBind12mWg_check :
    generatedAxisGlobalTwelveFifthBind12mWg.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem generatedAxisGlobalTwelveFifthBind12mD_ok :
    generatedAxisGlobalTwelveFifthBind12pDh.ok = true ∧
      generatedAxisGlobalTwelveFifthBind12mDg.ok = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `h₁₂` evaluate the word on the generators. -/
theorem generatedAxisGlobalTwelveFifthBind12Dh_cols : ∀ i : Fin 24,
    qmWordP (generatedAxisGlobalTwelveFifthBind12pWh.map Prod.snd) (2 ^ i.val, false) =
      (fld 24 generatedAxisGlobalTwelveFifthBind12pDh.colsP i.val,
        generatedAxisGlobalTwelveFifthBind12pDh.coeff.testBit i.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `g` evaluate the word on the generators. -/
theorem generatedAxisGlobalTwelveFifthBind12mDg_cols : ∀ i : Fin 24,
    qmWordP (generatedAxisGlobalTwelveFifthBind12mWg.map Prod.snd) (2 ^ i.val, false) =
      (fld 24 generatedAxisGlobalTwelveFifthBind12mDg.colsP i.val,
        generatedAxisGlobalTwelveFifthBind12mDg.coeff.testBit i.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `h₁₂`. -/
theorem generatedAxisGlobalTwelveFifthBind12Dh_rows : ∀ i : Fin 24,
    fld 24 generatedAxisGlobalTwelveFifthBind12pDh.rowsP i.val =
      rowsOf (fun j => fld 24 generatedAxisGlobalTwelveFifthBind12pDh.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `g`. -/
theorem generatedAxisGlobalTwelveFifthBind12mDg_rows : ∀ i : Fin 24,
    fld 24 generatedAxisGlobalTwelveFifthBind12mDg.rowsP i.val =
      rowsOf (fun j => fld 24 generatedAxisGlobalTwelveFifthBind12mDg.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `h₁₂ v₅` is transported onto the literal targets. -/
theorem generatedAxisGlobalTwelveFifthBind12Th_check :
    shortCheckF generatedAxisGlobalTwelveFifthBind12pDh fifthSrcShort.flat
      generatedAxisGlobalTwelveFifthBind12pTh = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `g v₄` is transported onto the literal targets. -/
theorem generatedAxisGlobalTwelveFifthBind12mTg_check :
    shortCheckF generatedAxisGlobalTwelveFifthBind12mDg fourthSrcShort.flat
      generatedAxisGlobalTwelveFifthBind12mTg = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem generatedAxisGlobalTwelveFifthBind12mT_labels :
    generatedAxisGlobalTwelveFifthBind12pTh.all (fun p => decide (p.1 < 98280)) = true ∧
      generatedAxisGlobalTwelveFifthBind12mTg.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The word bound of `h₁₂`. -/
theorem generatedAxisGlobalTwelveFifthBind12H_growth :
    tensorWordGrowthAll generatedAxisGlobalTwelveFifthBind12H * 64 = 4194304 := by decide

/-- The word bound of `g`. -/
theorem generatedAxisGlobalTwelveFifthBind12mG_growth :
    tensorWordGrowthAll generatedAxisGlobalTwelveFifthBind12mG * 56 = 114688 := by decide

/-- The coordinates of `h₁₂ v₅`. -/
theorem generatedAxisGlobalTwelveFifthBind12L_actual :
    griessConwayEncode (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBind12H)
      (generatedAxisGlobalTwelveRepresentative 4)) = generatedAxisGlobalTwelveFifthBind12L.real :=
  IdentVec.word_actual (fifthSrcVecW 64) generatedAxisGlobalTwelveFifthBind12pWh
    generatedAxisGlobalTwelveFifthBind12Wh_check generatedAxisGlobalTwelveFifthBind12pDh
    generatedAxisGlobalTwelveFifthBind12mD_ok.1 generatedAxisGlobalTwelveFifthBind12Dh_cols
    generatedAxisGlobalTwelveFifthBind12Dh_rows generatedAxisGlobalTwelveFifthBind12pTh
    generatedAxisGlobalTwelveFifthBind12Th_check _
    (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind12H (fifthSrcXW_bnd (by norm_num))
      (by rw [generatedAxisGlobalTwelveFifthBind12H_growth]; norm_num) 1).2 _
    (fifthSrcW_rep (by norm_num))

/-- The coordinates of `g v₄`. -/
theorem generatedAxisGlobalTwelveFifthBind12mW_actual :
    griessConwayEncode (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBind12mG)
      (generatedAxisGlobalTwelveRepresentative 3)) = generatedAxisGlobalTwelveFifthBind12mW.real :=
  IdentVec.word_actual (fourthSrcVecW 64) generatedAxisGlobalTwelveFifthBind12mWg
    generatedAxisGlobalTwelveFifthBind12mWg_check generatedAxisGlobalTwelveFifthBind12mDg
    generatedAxisGlobalTwelveFifthBind12mD_ok.2 generatedAxisGlobalTwelveFifthBind12mDg_cols
    generatedAxisGlobalTwelveFifthBind12mDg_rows generatedAxisGlobalTwelveFifthBind12mTg
    generatedAxisGlobalTwelveFifthBind12mTg_check _
    (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind12mG (fourthSrcXW_bnd (by norm_num))
      (by rw [generatedAxisGlobalTwelveFifthBind12mG_growth]; norm_num) 1).2 _
    (fourthSrcW_rep (by norm_num))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
