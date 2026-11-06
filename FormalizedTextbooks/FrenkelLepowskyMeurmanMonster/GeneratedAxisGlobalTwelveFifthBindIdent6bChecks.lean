/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindIdent6Checks
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindIdent6abData

/-! # Target-side data checks of the Fifth identification (I6-) at the root 6 representative

The source side `h₆ v₅` is certified in `GeneratedAxisGlobalTwelveFifthBindIdent6Checks`
(`generatedAxisGlobalTwelveFifthBind6pL`, `generatedAxisGlobalTwelveFifthBind6pL_actual`). This
module certifies the literal target data of `GeneratedAxisGlobalTwelveFifthBindIdent6abData` and
binds the target representation `g v₅` to the genuine coordinates, as in gident's pilot. The
identification itself is not asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The destination word `g`. -/
def generatedAxisGlobalTwelveFifthBind6bG : List IdentLetter :=
  generatedAxisGlobalTwelveFifthBind6bWg.map Prod.fst

/-- The packed tensor of `g v₅`. -/
def generatedAxisGlobalTwelveFifthBind6bWX : List SVec :=
  tensorWordAll 64 generatedAxisGlobalTwelveFifthBind6bG (fifthSrcXW 64)

/-- The representation of `g v₅`. -/
def generatedAxisGlobalTwelveFifthBind6bW : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet generatedAxisGlobalTwelveFifthBind6bG,
    ShortData.ofList generatedAxisGlobalTwelveFifthBind6bTg, 1 / 16,
    tensorRat 64 generatedAxisGlobalTwelveFifthBind6bWX
      ((tensorWordDenAll generatedAxisGlobalTwelveFifthBind6bG : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of `g` are certified. -/
theorem generatedAxisGlobalTwelveFifthBind6bWg_check :
    generatedAxisGlobalTwelveFifthBind6bWg.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem generatedAxisGlobalTwelveFifthBind6bDg_ok :
    generatedAxisGlobalTwelveFifthBind6bDg.ok = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `g` evaluate the word on the generators. -/
theorem generatedAxisGlobalTwelveFifthBind6bDg_cols : ∀ i : Fin 24,
    qmWordP (generatedAxisGlobalTwelveFifthBind6bWg.map Prod.snd) (2 ^ i.val, false) =
      (fld 24 generatedAxisGlobalTwelveFifthBind6bDg.colsP i.val,
        generatedAxisGlobalTwelveFifthBind6bDg.coeff.testBit i.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `g`. -/
theorem generatedAxisGlobalTwelveFifthBind6bDg_rows : ∀ i : Fin 24,
    fld 24 generatedAxisGlobalTwelveFifthBind6bDg.rowsP i.val =
      rowsOf (fun j => fld 24 generatedAxisGlobalTwelveFifthBind6bDg.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `g v₅` is transported onto the literal targets. -/
theorem generatedAxisGlobalTwelveFifthBind6bTg_check :
    shortCheckF generatedAxisGlobalTwelveFifthBind6bDg fifthSrcShort.flat
      generatedAxisGlobalTwelveFifthBind6bTg = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem generatedAxisGlobalTwelveFifthBind6bTg_labels :
    generatedAxisGlobalTwelveFifthBind6bTg.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The word bound of `g`. -/
theorem generatedAxisGlobalTwelveFifthBind6bG_growth :
    tensorWordGrowthAll generatedAxisGlobalTwelveFifthBind6bG * 64 = 33554432 := by decide

/-- The coordinates of `g v₅`. -/
theorem generatedAxisGlobalTwelveFifthBind6bW_actual :
    griessConwayEncode (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBind6bG)
      (generatedAxisGlobalTwelveRepresentative 4)) = generatedAxisGlobalTwelveFifthBind6bW.real :=
  IdentVec.word_actual (fifthSrcVecW 64) generatedAxisGlobalTwelveFifthBind6bWg
    generatedAxisGlobalTwelveFifthBind6bWg_check generatedAxisGlobalTwelveFifthBind6bDg
    generatedAxisGlobalTwelveFifthBind6bDg_ok generatedAxisGlobalTwelveFifthBind6bDg_cols
    generatedAxisGlobalTwelveFifthBind6bDg_rows generatedAxisGlobalTwelveFifthBind6bTg
    generatedAxisGlobalTwelveFifthBind6bTg_check _
    (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind6bG (fifthSrcXW_bnd (by norm_num))
      (by rw [generatedAxisGlobalTwelveFifthBind6bG_growth]; norm_num) 1).2 _
    (fifthSrcW_rep (by norm_num))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
