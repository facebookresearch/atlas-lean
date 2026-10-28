/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17mData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification data checks: the image of the Root8 source under `e17mW`

The representation `e17mVW` of `e17mW v` (`v` the Root8 representative `9`): matrix block by the spatial
alphabet, short block by the checked transport of `srcRootEightCShort` onto the packed target chunks `e17mTW`, tensor
block by the fused plan `e17mPlanW` on `rootEightSrcXL 64` (`tensorPlanS_actual`); binding `e17mVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e17mW v`. -/
def e17mXW : List SVec := tensorPlanS 64 e17mPlanW (rootEightSrcXL 64)

/-- The tensor scale of `e17mW v`. -/
def e17mEW : ℚ := (tensorWordDenAll e17mW : ℚ) * 32

/-- The representation of `e17mW v`. -/
def e17mVW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet e17mW, ShortData.ofList (OctadDense.octChunkTerms e17mTW),
    (1 / 128), tensorRat 64 e17mXW e17mEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e17mW` are certified. -/
theorem e17mWW_check : e17mWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e17mDW_ok : e17mDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e17mDW_cols : ∀ i : Fin 24, qmWordP (e17mWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e17mDW.colsP i.val, e17mDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e17mDW_rows : ∀ i : Fin 24,
    fld 24 e17mDW.rowsP i.val = rowsOf (fun j => fld 24 e17mDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e17mTW_check0 :
    shortCheckPk e17mDW 10 15 ((srcRootEightCShort.flat).take 15360) (((OctadDense.octChunkTerms e17mTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e17mTW_check1 :
    shortCheckPk e17mDW 10 15 (((srcRootEightCShort.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e17mTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e17mTW_check2 :
    shortCheckPk e17mDW 10 3 (((srcRootEightCShort.flat).drop 15360).drop 15360) ((((OctadDense.octChunkTerms e17mTW)).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e17mTW_check : shortCheckF e17mDW srcRootEightCShort.flat (OctadDense.octChunkTerms e17mTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e17mTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e17mTW_check1)
    (shortCheckPk_sound _ 10 3 _ _ e17mTW_check2))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e17mTW_labels :
    (OctadDense.octChunkTerms e17mTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e17mPlanW_word : planWord e17mPlanW = e17mW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e17mPlanW_ok : planOk e17mPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e17mW_growth : tensorWordGrowthAll e17mW = 34359738368 := by decide +kernel

/-- The tensor bound of `e17mW v`. -/
theorem e17mXW_bnd : TBnd 64 (34359738368 * 15) e17mXW := by
  have h := (tensorPlanS_actual e17mPlanW e17mPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e17mPlanW_word, e17mW_growth]; norm_num) 32).1
  rw [e17mPlanW_word, e17mW_growth] at h
  exact h

/-- The coordinates of `e17mW v`. -/
theorem e17mVW_actual : griessConwayEncode (rhoLocal (identWordLocal e17mW)
    (generatedAxisGlobalTwelveRepresentative 9)) = e17mVW.real := by
  have hT := (tensorPlanS_actual e17mPlanW e17mPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e17mPlanW_word, e17mW_growth]; norm_num) 32).2
  rw [e17mPlanW_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) e17mWW e17mWW_check e17mDW e17mDW_ok e17mDW_cols
    e17mDW_rows _ e17mTW_check _ hT _ (rootEightSrcL_rep (by norm_num))

/-- The short block of `e17mW v` satisfies the range conditions. -/
theorem e17mVW_ok : e17mVW.sh.ok = true := ofList_ok _ e17mTW_labels

/-- The short block of `e17mW v` in chunk form. -/
theorem e17mVW_sh : e17mVW.sh = ShortData.ofList (OctadDense.octChunkTerms e17mTW) := rfl

/-- The tensor block of `e17mW v`. -/
theorem e17mVW_ten : e17mVW.ten = tensorRat 64 e17mXW e17mEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
