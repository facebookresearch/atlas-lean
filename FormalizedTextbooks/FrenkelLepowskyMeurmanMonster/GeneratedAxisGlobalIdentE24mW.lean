/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24mData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh

/-! # Dense identification data checks: the image of the Seventh source under `e24mW`

The representation `e24mVW` of `e24mW v` (`v` the Seventh representative `6`): matrix block by the spatial
alphabet, short block by the checked transport of `seventhShS` onto the packed target chunks `e24mTW`, tensor
block by the fused plan `e24mPlanW` on `srcSeventhX0F 64` (`tensorPlanS_actual`); binding `e24mVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e24mW v`. -/
def e24mXW : List SVec := tensorPlanS 64 e24mPlanW (srcSeventhX0F 64)

/-- The tensor scale of `e24mW v`. -/
def e24mEW : ℚ := (tensorWordDenAll e24mW : ℚ) * srcSeventhD0

/-- The representation of `e24mW v`. -/
def e24mVW : IdentVec :=
  ⟨srcSeventhMat.act identSpatialAlphabet e24mW, ShortData.ofList (OctadDense.octChunkTerms e24mTW),
    (1 / 32), tensorRat 64 e24mXW e24mEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e24mW` are certified. -/
theorem e24mWW_check : e24mWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e24mDW_ok : e24mDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e24mDW_cols : ∀ i : Fin 24, qmWordP (e24mWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e24mDW.colsP i.val, e24mDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e24mDW_rows : ∀ i : Fin 24,
    fld 24 e24mDW.rowsP i.val = rowsOf (fun j => fld 24 e24mDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source is transported onto the target chunks. -/
theorem e24mTW_check : shortCheckF e24mDW seventhShS.flat (OctadDense.octChunkTerms e24mTW) = true :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e24mTW_labels :
    (OctadDense.octChunkTerms e24mTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e24mPlanW_word : planWord e24mPlanW = e24mW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e24mPlanW_ok : planOk e24mPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e24mW_growth : tensorWordGrowthAll e24mW = 524288 := by decide +kernel

/-- The tensor bound of `e24mW v`. -/
theorem e24mXW_bnd : TBnd 64 (524288 * (4 * (16777216 * 8) + 276 * 6144)) e24mXW := by
  have h := (tensorPlanS_actual e24mPlanW e24mPlanW_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [e24mPlanW_word, e24mW_growth]; norm_num) srcSeventhD0).1
  rw [e24mPlanW_word, e24mW_growth] at h
  exact h

/-- The coordinates of `e24mW v`. -/
theorem e24mVW_actual : griessConwayEncode (rhoLocal (identWordLocal e24mW)
    (generatedAxisGlobalTwelveRepresentative 6)) = e24mVW.real := by
  have hT := (tensorPlanS_actual e24mPlanW e24mPlanW_ok (srcSeventhX0F_bnd (w := 64) (by norm_num))
    (by rw [e24mPlanW_word, e24mW_growth]; norm_num) srcSeventhD0).2
  rw [e24mPlanW_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 64) e24mWW e24mWW_check e24mDW e24mDW_ok e24mDW_cols
    e24mDW_rows _ e24mTW_check _ hT _ (seventhSrcS_rep (by norm_num))

/-- The short block of `e24mW v` satisfies the range conditions. -/
theorem e24mVW_ok : e24mVW.sh.ok = true := ofList_ok _ e24mTW_labels

/-- The short block of `e24mW v` in chunk form. -/
theorem e24mVW_sh : e24mVW.sh = ShortData.ofList (OctadDense.octChunkTerms e24mTW) := rfl

/-- The tensor block of `e24mW v`. -/
theorem e24mVW_ten : e24mVW.ten = tensorRat 64 e24mXW e24mEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
