/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21xData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification data checks: the image of the Seventh source under `e21xW`

The representation `e21xVW` of `e21xW v` (`v` the Seventh representative `6`): matrix block by the spatial
alphabet, short block by the checked transport of `seventhShS` onto the packed target chunks `e21xTW`, tensor
block by the fused plan `e21xPlanW` on `srcSeventhX0F 64` (`tensorPlanS_actual`); binding `e21xVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e21xW v`. -/
def e21xXW : List SVec := tensorPlanS 64 e21xPlanW (srcSeventhX0F 64)

/-- The tensor scale of `e21xW v`. -/
def e21xEW : ℚ := (tensorWordDenAll e21xW : ℚ) * srcSeventhD0

/-- The representation of `e21xW v`. -/
def e21xVW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet e21xW, ShortData.ofList (OctadDense.octChunkTerms e21xTW),
    (1 / 32), tensorRat 64 e21xXW e21xEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e21xW` are certified. -/
theorem e21xWW_check : e21xWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e21xDW_ok : e21xDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e21xDW_cols : ∀ i : Fin 24, qmWordP (e21xWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e21xDW.colsP i.val, e21xDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e21xDW_rows : ∀ i : Fin 24,
    fld 24 e21xDW.rowsP i.val = rowsOf (fun j => fld 24 e21xDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source is transported onto the target chunks. -/
theorem e21xTW_check : shortCheckF e21xDW seventhShS.flat (OctadDense.octChunkTerms e21xTW) = true :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e21xTW_labels :
    (OctadDense.octChunkTerms e21xTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e21xPlanW_word : planWord e21xPlanW = e21xW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e21xPlanW_ok : planOk e21xPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e21xW_growth : tensorWordGrowthAll e21xW = 134217728 := by decide +kernel

/-- The tensor bound of `e21xW v`. -/
theorem e21xXW_bnd : TBnd 64 (134217728 * (4 * (16777216 * 8) + 276 * 6144)) e21xXW := by
  have h := (tensorPlanS_actual e21xPlanW e21xPlanW_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [e21xPlanW_word, e21xW_growth]; norm_num) srcSeventhD0).1
  rw [e21xPlanW_word, e21xW_growth] at h
  exact h

set_option maxRecDepth 100000 in
/-- The packed tight-bound check of the tensor of `e21xW v`. -/
theorem e21xXW_tchk : (List.range 24).all (fun i => colLeB 64 274877906944 (tcol e21xXW i)) = true := by
  decide +kernel

/-- The tight bound of the tensor of `e21xW v`. -/
theorem e21xXW_tight : TBnd 64 274877906944 e21xXW :=
  tbnd_of_check (by norm_num) e21xXW_bnd (by norm_num) (by norm_num) e21xXW_tchk

/-- The coordinates of `e21xW v`. -/
theorem e21xVW_actual : griessConwayEncode (rhoLocal (identWordLocal e21xW)
    (generatedAxisGlobalTwelveRepresentative 6)) = e21xVW.real := by
  have hT := (tensorPlanS_actual e21xPlanW e21xPlanW_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [e21xPlanW_word, e21xW_growth]; norm_num) srcSeventhD0).2
  rw [e21xPlanW_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 64) e21xWW e21xWW_check e21xDW e21xDW_ok e21xDW_cols
    e21xDW_rows _ e21xTW_check _ hT _ (seventhSrcS_rep (by norm_num))

/-- The short block of `e21xW v` satisfies the range conditions. -/
theorem e21xVW_ok : e21xVW.sh.ok = true := ofList_ok _ e21xTW_labels

/-- The short block of `e21xW v` in chunk form. -/
theorem e21xVW_sh : e21xVW.sh = ShortData.ofList (OctadDense.octChunkTerms e21xTW) := rfl

/-- The tensor block of `e21xW v`. -/
theorem e21xVW_ten : e21xVW.ten = tensorRat 64 e21xXW e21xEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
