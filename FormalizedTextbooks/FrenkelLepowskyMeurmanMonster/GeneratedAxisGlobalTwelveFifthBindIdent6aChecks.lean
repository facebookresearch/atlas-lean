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

/-! # Target-side data checks of the Fifth identification (I6+) at the root 6 representative

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
def generatedAxisGlobalTwelveFifthBind6aG : List IdentLetter :=
  generatedAxisGlobalTwelveFifthBind6aWg.map Prod.fst

/-- The packed tensor of `g v₅`. -/
def generatedAxisGlobalTwelveFifthBind6aWX : List SVec :=
  tensorWordAll 64 generatedAxisGlobalTwelveFifthBind6aG (fifthSrcXW 64)

/-- The representation of `g v₅`. -/
def generatedAxisGlobalTwelveFifthBind6aW : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet generatedAxisGlobalTwelveFifthBind6aG,
    ShortData.ofList generatedAxisGlobalTwelveFifthBind6aTg, 1 / 16,
    tensorRat 64 generatedAxisGlobalTwelveFifthBind6aWX
      ((tensorWordDenAll generatedAxisGlobalTwelveFifthBind6aG : ℚ) * 1)⟩

set_option maxRecDepth 100000 in
/-- The letter data of `g` are certified. -/
theorem generatedAxisGlobalTwelveFifthBind6aWg_check :
    generatedAxisGlobalTwelveFifthBind6aWg.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem generatedAxisGlobalTwelveFifthBind6aDg_ok :
    generatedAxisGlobalTwelveFifthBind6aDg.ok = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of `g` evaluate the word on the generators. -/
theorem generatedAxisGlobalTwelveFifthBind6aDg_cols : ∀ i : Fin 24,
    qmWordP (generatedAxisGlobalTwelveFifthBind6aWg.map Prod.snd) (2 ^ i.val, false) =
      (fld 24 generatedAxisGlobalTwelveFifthBind6aDg.colsP i.val,
        generatedAxisGlobalTwelveFifthBind6aDg.coeff.testBit i.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of `g`. -/
theorem generatedAxisGlobalTwelveFifthBind6aDg_rows : ∀ i : Fin 24,
    fld 24 generatedAxisGlobalTwelveFifthBind6aDg.rowsP i.val =
      rowsOf (fun j => fld 24 generatedAxisGlobalTwelveFifthBind6aDg.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of `g v₅` is transported onto the literal targets. -/
theorem generatedAxisGlobalTwelveFifthBind6aTg_check :
    shortCheckF generatedAxisGlobalTwelveFifthBind6aDg fifthSrcShort.flat
      generatedAxisGlobalTwelveFifthBind6aTg = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The target list has valid labels. -/
theorem generatedAxisGlobalTwelveFifthBind6aTg_labels :
    generatedAxisGlobalTwelveFifthBind6aTg.all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The word bound of `g`. -/
theorem generatedAxisGlobalTwelveFifthBind6aG_growth :
    tensorWordGrowthAll generatedAxisGlobalTwelveFifthBind6aG * 64 = 33554432 := by decide

/-- The coordinates of `g v₅`. -/
theorem generatedAxisGlobalTwelveFifthBind6aW_actual :
    griessConwayEncode (rhoLocal (identWordLocal generatedAxisGlobalTwelveFifthBind6aG)
      (generatedAxisGlobalTwelveRepresentative 4)) = generatedAxisGlobalTwelveFifthBind6aW.real :=
  IdentVec.word_actual (fifthSrcVecW 64) generatedAxisGlobalTwelveFifthBind6aWg
    generatedAxisGlobalTwelveFifthBind6aWg_check generatedAxisGlobalTwelveFifthBind6aDg
    generatedAxisGlobalTwelveFifthBind6aDg_ok generatedAxisGlobalTwelveFifthBind6aDg_cols
    generatedAxisGlobalTwelveFifthBind6aDg_rows generatedAxisGlobalTwelveFifthBind6aTg
    generatedAxisGlobalTwelveFifthBind6aTg_check _
    (tensorWordAll_actual generatedAxisGlobalTwelveFifthBind6aG (fifthSrcXW_bnd (by norm_num))
      (by rw [generatedAxisGlobalTwelveFifthBind6aG_growth]; norm_num) 1).2 _
    (fifthSrcW_rep (by norm_num))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
