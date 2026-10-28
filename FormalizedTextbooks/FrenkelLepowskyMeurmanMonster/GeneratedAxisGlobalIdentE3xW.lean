/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3xData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Dense identification data checks: the image of the Sixth source under `e3xW`

The representation `e3xVW` of `e3xW v` (`v` the Sixth representative `5`): matrix block by the spatial
alphabet, short block by the checked transport of `sixthLitShort` onto the packed target chunks `e3xTW`, tensor
block by the fused plan `e3xPlanW` on `sixthSXF 64` (`tensorPlanS_actual`); binding `e3xVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e3xW v`. -/
def e3xXW : List SVec := tensorPlanS 64 e3xPlanW (sixthSXF 64)

/-- The tensor scale of `e3xW v`. -/
def e3xEW : ℚ := (tensorWordDenAll e3xW : ℚ) * 32

/-- The representation of `e3xW v`. -/
def e3xVW : IdentVec :=
  ⟨sixthSrcMat.act identSpatialAlphabet e3xW, ShortData.ofList (OctadDense.octChunkTerms e3xTW),
    1 / 32, tensorRat 64 e3xXW e3xEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e3xW` are certified. -/
theorem e3xWW_check : e3xWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e3xDW_ok : e3xDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e3xDW_cols : ∀ i : Fin 24, qmWordP (e3xWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e3xDW.colsP i.val, e3xDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e3xDW_rows : ∀ i : Fin 24,
    fld 24 e3xDW.rowsP i.val = rowsOf (fun j => fld 24 e3xDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e3xTW_check0 :
    shortCheckPk e3xDW 10 15 ((sixthLitShort.flat).take 15360) (((OctadDense.octChunkTerms e3xTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e3xTW_check1 :
    shortCheckPk e3xDW 10 15 ((sixthLitShort.flat).drop 15360) (((OctadDense.octChunkTerms e3xTW)).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e3xTW_check : shortCheckF e3xDW sixthLitShort.flat (OctadDense.octChunkTerms e3xTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e3xTW_check0)
    (shortCheckPk_sound _ 10 15 _ _ e3xTW_check1)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e3xTW_labels :
    (OctadDense.octChunkTerms e3xTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e3xPlanW_word : planWord e3xPlanW = e3xW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e3xPlanW_ok : planOk e3xPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e3xW_growth : tensorWordGrowthAll e3xW = 134217728 := by decide +kernel

/-- The tensor bound of `e3xW v`. -/
theorem e3xXW_bnd : TBnd 64 (134217728 * (2 ^ 8 - 1)) e3xXW := by
  have h := (tensorPlanS_actual e3xPlanW e3xPlanW_ok (sixthSXF_bndF (w := 64) (by norm_num))
    (by rw [e3xPlanW_word, e3xW_growth]; norm_num) 32).1
  rw [e3xPlanW_word, e3xW_growth] at h
  exact h

/-- The coordinates of `e3xW v`. -/
theorem e3xVW_actual : griessConwayEncode (rhoLocal (identWordLocal e3xW)
    (generatedAxisGlobalTwelveRepresentative 5)) = e3xVW.real := by
  have hT := (tensorPlanS_actual e3xPlanW e3xPlanW_ok (sixthSXF_bndF (w := 64) (by norm_num))
    (by rw [e3xPlanW_word, e3xW_growth]; norm_num) 32).2
  rw [e3xPlanW_word] at hT
  exact IdentVec.word_actual (sixthSrcVecF 64) e3xWW e3xWW_check e3xDW e3xDW_ok e3xDW_cols
    e3xDW_rows _ e3xTW_check _ hT _ (sixthSrcF_rep (by norm_num))

/-- The short block of `e3xW v` satisfies the range conditions. -/
theorem e3xVW_ok : e3xVW.sh.ok = true := ofList_ok _ e3xTW_labels

/-- The short block of `e3xW v` in chunk form. -/
theorem e3xVW_sh : e3xVW.sh = ShortData.ofList (OctadDense.octChunkTerms e3xTW) := rfl

/-- The tensor block of `e3xW v`. -/
theorem e3xVW_ten : e3xVW.ten = tensorRat 64 e3xXW e3xEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
