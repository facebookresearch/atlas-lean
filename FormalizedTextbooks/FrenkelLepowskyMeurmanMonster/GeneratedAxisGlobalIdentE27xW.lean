/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27xData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Dense identification data checks: the image of the Fourth source under `e27xW`

The representation `e27xVW` of `e27xW v` (`v` the Fourth representative `3`): matrix block by the spatial
alphabet, short block by the checked transport of `fourthSrcShort` onto the packed target chunks `e27xTW`, tensor
block by the fused plan `e27xPlanW` on `fourthSrcXW 64` (`tensorPlanS_actual`); binding `e27xVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e27xW v`. -/
def e27xXW : List SVec := tensorPlanS 64 e27xPlanW (fourthSrcXW 64)

/-- The tensor scale of `e27xW v`. -/
def e27xEW : ℚ := (tensorWordDenAll e27xW : ℚ) * 1

/-- The representation of `e27xW v`. -/
def e27xVW : IdentVec :=
  ⟨fourthSrcMat.act identSpatialAlphabet e27xW, ShortData.ofList (OctadDense.octChunkTerms e27xTW),
    1 / 8, tensorRat 64 e27xXW e27xEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e27xW` are certified. -/
theorem e27xWW_check : e27xWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e27xDW_ok : e27xDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e27xDW_cols : ∀ i : Fin 24, qmWordP (e27xWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e27xDW.colsP i.val, e27xDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e27xDW_rows : ∀ i : Fin 24,
    fld 24 e27xDW.rowsP i.val = rowsOf (fun j => fld 24 e27xDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source is transported onto the target chunks. -/
theorem e27xTW_check : shortCheckF e27xDW fourthSrcShort.flat (OctadDense.octChunkTerms e27xTW) = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e27xTW_labels :
    (OctadDense.octChunkTerms e27xTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e27xPlanW_word : planWord e27xPlanW = e27xW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e27xPlanW_ok : planOk e27xPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e27xW_growth : tensorWordGrowthAll e27xW = 524288 := by decide +kernel

/-- The tensor bound of `e27xW v`. -/
theorem e27xXW_bnd : TBnd 64 (524288 * 56) e27xXW := by
  have h := (tensorPlanS_actual e27xPlanW e27xPlanW_ok (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e27xPlanW_word, e27xW_growth]; norm_num) 1).1
  rw [e27xPlanW_word, e27xW_growth] at h
  exact h

/-- The coordinates of `e27xW v`. -/
theorem e27xVW_actual : griessConwayEncode (rhoLocal (identWordLocal e27xW)
    (generatedAxisGlobalTwelveRepresentative 3)) = e27xVW.real := by
  have hT := (tensorPlanS_actual e27xPlanW e27xPlanW_ok (fourthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e27xPlanW_word, e27xW_growth]; norm_num) 1).2
  rw [e27xPlanW_word] at hT
  exact IdentVec.word_actual (fourthSrcVecW 64) e27xWW e27xWW_check e27xDW e27xDW_ok e27xDW_cols
    e27xDW_rows _ e27xTW_check _ hT _ (fourthSrcW_rep (by norm_num))

/-- The short block of `e27xW v` satisfies the range conditions. -/
theorem e27xVW_ok : e27xVW.sh.ok = true := ofList_ok _ e27xTW_labels

/-- The short block of `e27xW v` in chunk form. -/
theorem e27xVW_sh : e27xVW.sh = ShortData.ofList (OctadDense.octChunkTerms e27xTW) := rfl

/-- The tensor block of `e27xW v`. -/
theorem e27xVW_ten : e27xVW.ten = tensorRat 64 e27xXW e27xEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
