/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13mData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification data checks: the image of the Seventh source under `e13mW`

The representation `e13mVW` of `e13mW v` (`v` the Seventh representative `6`): matrix block by the spatial
alphabet, short block by the checked transport of `seventhShS` onto the packed target chunks `e13mTW`, tensor
block by the fused plan `e13mPlanW` on `srcSeventhX0F 64` (`tensorPlanS_actual`); binding `e13mVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e13mW v`. -/
def e13mXW : List SVec := tensorPlanS 64 e13mPlanW (srcSeventhX0F 64)

/-- The tensor scale of `e13mW v`. -/
def e13mEW : ℚ := (tensorWordDenAll e13mW : ℚ) * srcSeventhD0

/-- The representation of `e13mW v`. -/
def e13mVW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet e13mW, ShortData.ofList (OctadDense.octChunkTerms e13mTW),
    (1 / 32), tensorRat 64 e13mXW e13mEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e13mW` are certified. -/
theorem e13mWW_check : e13mWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e13mDW_ok : e13mDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e13mDW_cols : ∀ i : Fin 24, qmWordP (e13mWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e13mDW.colsP i.val, e13mDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e13mDW_rows : ∀ i : Fin 24,
    fld 24 e13mDW.rowsP i.val = rowsOf (fun j => fld 24 e13mDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source is transported onto the target chunks. -/
theorem e13mTW_check : shortCheckF e13mDW seventhShS.flat (OctadDense.octChunkTerms e13mTW) = true :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e13mTW_labels :
    (OctadDense.octChunkTerms e13mTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e13mPlanW_word : planWord e13mPlanW = e13mW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e13mPlanW_ok : planOk e13mPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e13mW_growth : tensorWordGrowthAll e13mW = 134217728 := by decide +kernel

/-- The tensor bound of `e13mW v`. -/
theorem e13mXW_bnd : TBnd 64 (134217728 * (4 * (16777216 * 8) + 276 * 6144)) e13mXW := by
  have h := (tensorPlanS_actual e13mPlanW e13mPlanW_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [e13mPlanW_word, e13mW_growth]; norm_num) srcSeventhD0).1
  rw [e13mPlanW_word, e13mW_growth] at h
  exact h

set_option maxRecDepth 100000 in
/-- The packed tight-bound check of the tensor of `e13mW v`. -/
theorem e13mXW_tchk : (List.range 24).all (fun i => colLeB 64 274877906944 (tcol e13mXW i)) = true := by
  decide +kernel

/-- The tight bound of the tensor of `e13mW v`. -/
theorem e13mXW_tight : TBnd 64 274877906944 e13mXW :=
  tbnd_of_check (by norm_num) e13mXW_bnd (by norm_num) (by norm_num) e13mXW_tchk

/-- The coordinates of `e13mW v`. -/
theorem e13mVW_actual : griessConwayEncode (rhoLocal (identWordLocal e13mW)
    (generatedAxisGlobalTwelveRepresentative 6)) = e13mVW.real := by
  have hT := (tensorPlanS_actual e13mPlanW e13mPlanW_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [e13mPlanW_word, e13mW_growth]; norm_num) srcSeventhD0).2
  rw [e13mPlanW_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 64) e13mWW e13mWW_check e13mDW e13mDW_ok e13mDW_cols
    e13mDW_rows _ e13mTW_check _ hT _ (seventhSrcS_rep (by norm_num))

/-- The short block of `e13mW v` satisfies the range conditions. -/
theorem e13mVW_ok : e13mVW.sh.ok = true := ofList_ok _ e13mTW_labels

/-- The short block of `e13mW v` in chunk form. -/
theorem e13mVW_sh : e13mVW.sh = ShortData.ofList (OctadDense.octChunkTerms e13mTW) := rfl

/-- The tensor block of `e13mW v`. -/
theorem e13mVW_ten : e13mVW.ten = tensorRat 64 e13mXW e13mEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
