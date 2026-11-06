/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16mData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification data checks: the image of the Root8 source under `e16mW`

The representation `e16mVW` of `e16mW v` (`v` the Root8 representative `9`): matrix block by the spatial
alphabet, short block by the checked transport of `srcRootEightCShort` onto the packed target chunks `e16mTW`, tensor
block by the fused plan `e16mPlanW` on `rootEightSrcXL 64` (`tensorPlanS_actual`); binding `e16mVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e16mW v`. -/
def e16mXW : List SVec := tensorPlanS 64 e16mPlanW (rootEightSrcXL 64)

/-- The tensor scale of `e16mW v`. -/
def e16mEW : ℚ := (tensorWordDenAll e16mW : ℚ) * 32

/-- The representation of `e16mW v`. -/
def e16mVW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet e16mW, ShortData.ofList (OctadDense.octChunkTerms e16mTW),
    (1 / 128), tensorRat 64 e16mXW e16mEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e16mW` are certified. -/
theorem e16mWW_check : e16mWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e16mDW_ok : e16mDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e16mDW_cols : ∀ i : Fin 24, qmWordP (e16mWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e16mDW.colsP i.val, e16mDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e16mDW_rows : ∀ i : Fin 24,
    fld 24 e16mDW.rowsP i.val = rowsOf (fun j => fld 24 e16mDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e16mTW_check0 :
    shortCheckPk e16mDW 10 15 ((srcRootEightCShort.flat).take 15360) (((OctadDense.octChunkTerms e16mTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e16mTW_check1 :
    shortCheckPk e16mDW 10 15 (((srcRootEightCShort.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e16mTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e16mTW_check2 :
    shortCheckPk e16mDW 10 3 (((srcRootEightCShort.flat).drop 15360).drop 15360) ((((OctadDense.octChunkTerms e16mTW)).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e16mTW_check : shortCheckF e16mDW srcRootEightCShort.flat (OctadDense.octChunkTerms e16mTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e16mTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e16mTW_check1)
    (shortCheckPk_sound _ 10 3 _ _ e16mTW_check2))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e16mTW_labels :
    (OctadDense.octChunkTerms e16mTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e16mPlanW_word : planWord e16mPlanW = e16mW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e16mPlanW_ok : planOk e16mPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e16mW_growth : tensorWordGrowthAll e16mW = 1073741824 := by decide +kernel

/-- The tensor bound of `e16mW v`. -/
theorem e16mXW_bnd : TBnd 64 (1073741824 * 15) e16mXW := by
  have h := (tensorPlanS_actual e16mPlanW e16mPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e16mPlanW_word, e16mW_growth]; norm_num) 32).1
  rw [e16mPlanW_word, e16mW_growth] at h
  exact h

/-- The coordinates of `e16mW v`. -/
theorem e16mVW_actual : griessConwayEncode (rhoLocal (identWordLocal e16mW)
    (generatedAxisGlobalTwelveRepresentative 9)) = e16mVW.real := by
  have hT := (tensorPlanS_actual e16mPlanW e16mPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e16mPlanW_word, e16mW_growth]; norm_num) 32).2
  rw [e16mPlanW_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) e16mWW e16mWW_check e16mDW e16mDW_ok e16mDW_cols
    e16mDW_rows _ e16mTW_check _ hT _ (rootEightSrcL_rep (by norm_num))

/-- The short block of `e16mW v` satisfies the range conditions. -/
theorem e16mVW_ok : e16mVW.sh.ok = true := ofList_ok _ e16mTW_labels

/-- The short block of `e16mW v` in chunk form. -/
theorem e16mVW_sh : e16mVW.sh = ShortData.ofList (OctadDense.octChunkTerms e16mTW) := rfl

/-- The tensor block of `e16mW v`. -/
theorem e16mVW_ten : e16mVW.ten = tensorRat 64 e16mXW e16mEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
