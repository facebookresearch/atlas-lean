/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindIdent0Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindTriangle
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord

/-! # Data checks of the Fifth identification (I0-) at the root 0 representative

Both sides are local images of the Fifth axis, as in gident's pilot
`GeneratedAxisGlobalIdentPilot1Checks`: the source `h₀ v₅` with
`h₀ = generatedAxisGlobalTwelveFifthBindCosetLetters 0` and the target `g v₅`. This module
certifies the literal data and binds both representations to the genuine coordinates. The
identification itself is not asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word `h₀`. -/
def generatedAxisGlobalTwelveFifthBind0H : List IdentLetter :=
  generatedAxisGlobalTwelveFifthBind0pWh.map Prod.fst

/-- The source word is the root 0 representative word. -/
theorem generatedAxisGlobalTwelveFifthBind0H_eq :
    generatedAxisGlobalTwelveFifthBind0H = generatedAxisGlobalTwelveFifthBindCosetLetters 0 :=
  rfl

/-- The destination word `g`. -/
def generatedAxisGlobalTwelveFifthBind0mG : List IdentLetter :=
  generatedAxisGlobalTwelveFifthBind0mWg.map Prod.fst

/-- The packed tensor of `h₀ v₅`. -/
def generatedAxisGlobalTwelveFifthBind0LX : List SVec :=
  tensorWordAll 64 generatedAxisGlobalTwelveFifthBind0H (fifthSrcXW 64)

/-- The packed tensor of `g v₅`. -/
def generatedAxisGlobalTwelveFifthBind0mWX : List SVec :=
  tensorWordAll 64 generatedAxisGlobalTwelveFifthBind0mG (fifthSrcXW 64)

/-- The representation of `h₀ v₅`. -/
def generatedAxisGlobalTwelveFifthBind0L : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet generatedAxisGlobalTwelveFifthBind0H,
    ShortData.ofList generatedAxisGlobalTwelveFifthBind0pTh, 1 / 16,
    tensorRat 64 generatedAxisGlobalTwelveFifthBind0LX
      ((tensorWordDenAll generatedAxisGlobalTwelveFifthBind0H : ℚ) * 1)⟩

/-- The representation of `g v₅`. -/
def generatedAxisGlobalTwelveFifthBind0mW : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet generatedAxisGlobalTwelveFifthBind0mG,
    ShortData.ofList generatedAxisGlobalTwelveFifthBind0mTg, 1 / 16,
    tensorRat 64 generatedAxisGlobalTwelveFifthBind0mWX
      ((tensorWordDenAll generatedAxisGlobalTwelveFifthBind0mG : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of `h₀` are certified. -/
theorem generatedAxisGlobalTwelveFifthBind0Wh_check :
    generatedAxisGlobalTwelveFifthBind0pWh.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The letter data of `g` are certified. -/
theorem generatedAxisGlobalTwelveFifthBind0mWg_check :
    generatedAxisGlobalTwelveFifthBind0mWg.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem generatedAxisGlobalTwelveFifthBind0mD_ok :
    generatedAxisGlobalTwelveFifthBind0pDh.ok = true ∧
      generatedAxisGlobalTwelveFifthBind0mDg.ok = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `h₀` evaluate the word on the generators. -/
theorem generatedAxisGlobalTwelveFifthBind0Dh_cols : ∀ i : Fin 24,
    qmWordP (generatedAxisGlobalTwelveFifthBind0pWh.map Prod.snd) (2 ^ i.val, false) =
      (fld 24 generatedAxisGlobalTwelveFifthBind0pDh.colsP i.val,
        generatedAxisGlobalTwelveFifthBind0pDh.coeff.testBit i.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `g` evaluate the word on the generators. -/
theorem generatedAxisGlobalTwelveFifthBind0mDg_cols : ∀ i : Fin 24,
    qmWordP (generatedAxisGlobalTwelveFifthBind0mWg.map Prod.snd) (2 ^ i.val, false) =
      (fld 24 generatedAxisGlobalTwelveFifthBind0mDg.colsP i.val,
        generatedAxisGlobalTwelveFifthBind0mDg.coeff.testBit i.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `h₀`. -/
theorem generatedAxisGlobalTwelveFifthBind0Dh_rows : ∀ i : Fin 24,
    fld 24 generatedAxisGlobalTwelveFifthBind0pDh.rowsP i.val =
      rowsOf (fun j => fld 24 generatedAxisGlobalTwelveFifthBind0pDh.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `g`. -/
theorem generatedAxisGlobalTwelveFifthBind0mDg_rows : ∀ i : Fin 24,
    fld 24 generatedAxisGlobalTwelveFifthBind0mDg.rowsP i.val =
      rowsOf (fun j => fld 24 generatedAxisGlobalTwelveFifthBind0mDg.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `h₀ v₅` is transported onto the literal targets. -/
theorem generatedAxisGlobalTwelveFifthBind0Th_check :
    shortCheckF generatedAxisGlobalTwelveFifthBind0pDh fifthSrcShort.flat
      generatedAxisGlobalTwelveFifthBind0pTh = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `g v₅` is transported onto the literal targets. -/
theorem generatedAxisGlobalTwelveFifthBind0mTg_check :
    shortCheckF generatedAxisGlobalTwelveFifthBind0mDg fifthSrcShort.flat
      generatedAxisGlobalTwelveFifthBind0mTg = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Both target lists have valid labels. -/
theorem generatedAxisGlobalTwelveFifthBind0mT_labels :
    generatedAxisGlobalTwelveFifthBind0pTh.all (fun p => decide (p.1 < 98280)) = true ∧
      generatedAxisGlobalTwelveFifthBind0mTg.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The word bound of `h₀`. -/
theorem generatedAxisGlobalTwelveFifthBind0H_growth :
    tensorWordGrowthAll generatedAxisGlobalTwelveFifthBind0H * 64 = 4194304 := by decide

/-- The word bound of `g`. -/
theorem generatedAxisGlobalTwelveFifthBind0mG_growth :
    tensorWordGrowthAll generatedAxisGlobalTwelveFifthBind0mG * 64 = 33554432 := by decide

/-- The coordinates of `h₀ v₅`. -/
theorem generatedAxisGlobalTwelveFifthBind0L_actual :
    griessConwayEncode (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBind0H)
      (generatedAxisGlobalTwelveRepresentative 4)) = generatedAxisGlobalTwelveFifthBind0L.real :=
  IdentVec.word_actual (fifthSrcVecW 64) generatedAxisGlobalTwelveFifthBind0pWh
    generatedAxisGlobalTwelveFifthBind0Wh_check generatedAxisGlobalTwelveFifthBind0pDh
    generatedAxisGlobalTwelveFifthBind0mD_ok.1 generatedAxisGlobalTwelveFifthBind0Dh_cols
    generatedAxisGlobalTwelveFifthBind0Dh_rows generatedAxisGlobalTwelveFifthBind0pTh
    generatedAxisGlobalTwelveFifthBind0Th_check _
    (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind0H (fifthSrcXW_bnd (by norm_num))
      (by rw [generatedAxisGlobalTwelveFifthBind0H_growth]; norm_num) 1).2 _
    (fifthSrcW_rep (by norm_num))

/-- The coordinates of `g v₅`. -/
theorem generatedAxisGlobalTwelveFifthBind0mW_actual :
    griessConwayEncode (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBind0mG)
      (generatedAxisGlobalTwelveRepresentative 4)) = generatedAxisGlobalTwelveFifthBind0mW.real :=
  IdentVec.word_actual (fifthSrcVecW 64) generatedAxisGlobalTwelveFifthBind0mWg
    generatedAxisGlobalTwelveFifthBind0mWg_check generatedAxisGlobalTwelveFifthBind0mDg
    generatedAxisGlobalTwelveFifthBind0mD_ok.2 generatedAxisGlobalTwelveFifthBind0mDg_cols
    generatedAxisGlobalTwelveFifthBind0mDg_rows generatedAxisGlobalTwelveFifthBind0mTg
    generatedAxisGlobalTwelveFifthBind0mTg_check _
    (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind0mG (fifthSrcXW_bnd (by norm_num))
      (by rw [generatedAxisGlobalTwelveFifthBind0mG_growth]; norm_num) 1).2 _
    (fifthSrcW_rep (by norm_num))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
