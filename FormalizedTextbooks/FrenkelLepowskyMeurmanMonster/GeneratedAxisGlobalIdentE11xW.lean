/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11xData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification data checks: the image of the Twelfth source under `e11xW`

The representation `e11xVW` of `e11xW v` (`v` the Twelfth representative `10`): matrix block by the spatial
alphabet, short block by the checked transport of `twelfthShS` onto the packed target chunks `e11xTW`, tensor
block by the fused plan `e11xPlanW` on `twelfthSrcXW 64` (`tensorPlanS_actual`); binding `e11xVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e11xW v`. -/
def e11xXW : List SVec := tensorPlanS 64 e11xPlanW (twelfthSrcXW 64)

/-- The tensor scale of `e11xW v`. -/
def e11xEW : ℚ := (tensorWordDenAll e11xW : ℚ) * 32

/-- The representation of `e11xW v`. -/
def e11xVW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet e11xW, ShortData.ofList (OctadDense.octChunkTerms e11xTW),
    (1 / 128), tensorRat 64 e11xXW e11xEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e11xW` are certified. -/
theorem e11xWW_check : e11xWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e11xDW_ok : e11xDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e11xDW_cols : ∀ i : Fin 24, qmWordP (e11xWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e11xDW.colsP i.val, e11xDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e11xDW_rows : ∀ i : Fin 24,
    fld 24 e11xDW.rowsP i.val = rowsOf (fun j => fld 24 e11xDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e11xTW_check0 :
    shortCheckPk e11xDW 10 15 ((twelfthShS.flat).take 15360) (((OctadDense.octChunkTerms e11xTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e11xTW_check1 :
    shortCheckPk e11xDW 10 15 (((twelfthShS.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e11xTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e11xTW_check2 :
    shortCheckPk e11xDW 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360) (((((OctadDense.octChunkTerms e11xTW)).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 3. -/
theorem e11xTW_check3 :
    shortCheckPk e11xDW 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360) (((((OctadDense.octChunkTerms e11xTW)).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e11xTW_check : shortCheckF e11xDW twelfthShS.flat (OctadDense.octChunkTerms e11xTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e11xTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e11xTW_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e11xTW_check2)
    (shortCheckPk_sound _ 10 1 _ _ e11xTW_check3)))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e11xTW_labels :
    (OctadDense.octChunkTerms e11xTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e11xPlanW_word : planWord e11xPlanW = e11xW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e11xPlanW_ok : planOk e11xPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e11xW_growth : tensorWordGrowthAll e11xW = 524288 := by decide +kernel

/-- The tensor bound of `e11xW v`. -/
theorem e11xXW_bnd : TBnd 64 (524288 * 15) e11xXW := by
  have h := (tensorPlanS_actual e11xPlanW e11xPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e11xPlanW_word, e11xW_growth]; norm_num) 32).1
  rw [e11xPlanW_word, e11xW_growth] at h
  exact h

/-- The coordinates of `e11xW v`. -/
theorem e11xVW_actual : griessConwayEncode (rhoLocal (identWordLocal e11xW)
    (generatedAxisGlobalTwelveRepresentative 10)) = e11xVW.real := by
  have hT := (tensorPlanS_actual e11xPlanW e11xPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e11xPlanW_word, e11xW_growth]; norm_num) 32).2
  rw [e11xPlanW_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) e11xWW e11xWW_check e11xDW e11xDW_ok e11xDW_cols
    e11xDW_rows _ e11xTW_check _ hT _ (twelfthSrcS_rep (by norm_num))

/-- The short block of `e11xW v` satisfies the range conditions. -/
theorem e11xVW_ok : e11xVW.sh.ok = true := ofList_ok _ e11xTW_labels

/-- The short block of `e11xW v` in chunk form. -/
theorem e11xVW_sh : e11xVW.sh = ShortData.ofList (OctadDense.octChunkTerms e11xTW) := rfl

/-- The tensor block of `e11xW v`. -/
theorem e11xVW_ten : e11xVW.ten = tensorRat 64 e11xXW e11xEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
