/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12xData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification data checks: the image of the Tenth source under `e12xW`

The representation `e12xVW` of `e12xW v` (`v` the Tenth representative `11`): matrix block by the spatial
alphabet, short block by the checked transport of `srcTenthCShort` onto the packed target chunks `e12xTW`, tensor
block by the fused plan `e12xPlanW` on `tenthSrcXL 64` (`tensorPlanS_actual`); binding `e12xVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e12xW v`. -/
def e12xXW : List SVec := tensorPlanS 64 e12xPlanW (tenthSrcXL 64)

/-- The tensor scale of `e12xW v`. -/
def e12xEW : ℚ := (tensorWordDenAll e12xW : ℚ) * 32

/-- The representation of `e12xW v`. -/
def e12xVW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet e12xW, ShortData.ofList (OctadDense.octChunkTerms e12xTW),
    (1 / 128), tensorRat 64 e12xXW e12xEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e12xW` are certified. -/
theorem e12xWW_check : e12xWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e12xDW_ok : e12xDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e12xDW_cols : ∀ i : Fin 24, qmWordP (e12xWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e12xDW.colsP i.val, e12xDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e12xDW_rows : ∀ i : Fin 24,
    fld 24 e12xDW.rowsP i.val = rowsOf (fun j => fld 24 e12xDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e12xTW_check0 :
    shortCheckPk e12xDW 10 15 ((srcTenthCShort.flat).take 15360) (((OctadDense.octChunkTerms e12xTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e12xTW_check1 :
    shortCheckPk e12xDW 10 15 (((srcTenthCShort.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e12xTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e12xTW_check2 :
    shortCheckPk e12xDW 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take 15360) (((((OctadDense.octChunkTerms e12xTW)).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 3. -/
theorem e12xTW_check3 :
    shortCheckPk e12xDW 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop 15360) (((((OctadDense.octChunkTerms e12xTW)).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e12xTW_check : shortCheckF e12xDW srcTenthCShort.flat (OctadDense.octChunkTerms e12xTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e12xTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e12xTW_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e12xTW_check2)
    (shortCheckPk_sound _ 10 1 _ _ e12xTW_check3)))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e12xTW_labels :
    (OctadDense.octChunkTerms e12xTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e12xPlanW_word : planWord e12xPlanW = e12xW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e12xPlanW_ok : planOk e12xPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e12xW_growth : tensorWordGrowthAll e12xW = 34359738368 := by decide +kernel

/-- The tensor bound of `e12xW v`. -/
theorem e12xXW_bnd : TBnd 64 (34359738368 * 15) e12xXW := by
  have h := (tensorPlanS_actual e12xPlanW e12xPlanW_ok (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e12xPlanW_word, e12xW_growth]; norm_num) 32).1
  rw [e12xPlanW_word, e12xW_growth] at h
  exact h

/-- The coordinates of `e12xW v`. -/
theorem e12xVW_actual : griessConwayEncode (rhoLocal (identWordLocal e12xW)
    (generatedAxisGlobalTwelveRepresentative 11)) = e12xVW.real := by
  have hT := (tensorPlanS_actual e12xPlanW e12xPlanW_ok (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e12xPlanW_word, e12xW_growth]; norm_num) 32).2
  rw [e12xPlanW_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) e12xWW e12xWW_check e12xDW e12xDW_ok e12xDW_cols
    e12xDW_rows _ e12xTW_check _ hT _ (tenthSrcL_rep (by norm_num))

/-- The short block of `e12xW v` satisfies the range conditions. -/
theorem e12xVW_ok : e12xVW.sh.ok = true := ofList_ok _ e12xTW_labels

/-- The short block of `e12xW v` in chunk form. -/
theorem e12xVW_sh : e12xVW.sh = ShortData.ofList (OctadDense.octChunkTerms e12xTW) := rfl

/-- The tensor block of `e12xW v`. -/
theorem e12xVW_ten : e12xVW.ten = tensorRat 64 e12xXW e12xEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
