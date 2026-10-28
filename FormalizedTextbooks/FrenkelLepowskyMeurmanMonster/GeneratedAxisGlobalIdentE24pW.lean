/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Dense identification data checks: the image of the Sixth source under `e24pW`

The representation `e24pVW` of `e24pW v` (`v` the Sixth representative `5`): matrix block by the spatial
alphabet, short block by the checked transport of `sixthLitShort` onto the packed target chunks `e24pTW`, tensor
block by the fused plan `e24pPlanW` on `sixthSXF 64` (`tensorPlanS_actual`); binding `e24pVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e24pW v`. -/
def e24pXW : List SVec := tensorPlanS 64 e24pPlanW (sixthSXF 64)

/-- The tensor scale of `e24pW v`. -/
def e24pEW : ℚ := (tensorWordDenAll e24pW : ℚ) * 32

/-- The representation of `e24pW v`. -/
def e24pVW : IdentVec :=
  ⟨sixthSrcMat.act identSpatialAlphabet e24pW, ShortData.ofList (OctadDense.octChunkTerms e24pTW),
    1 / 32, tensorRat 64 e24pXW e24pEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e24pW` are certified. -/
theorem e24pWW_check : e24pWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e24pDW_ok : e24pDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e24pDW_cols : ∀ i : Fin 24, qmWordP (e24pWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e24pDW.colsP i.val, e24pDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e24pDW_rows : ∀ i : Fin 24,
    fld 24 e24pDW.rowsP i.val = rowsOf (fun j => fld 24 e24pDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e24pTW_check0 :
    shortCheckPk e24pDW 10 15 ((sixthLitShort.flat).take 15360) (((OctadDense.octChunkTerms e24pTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e24pTW_check1 :
    shortCheckPk e24pDW 10 15 ((sixthLitShort.flat).drop 15360) (((OctadDense.octChunkTerms e24pTW)).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e24pTW_check : shortCheckF e24pDW sixthLitShort.flat (OctadDense.octChunkTerms e24pTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e24pTW_check0)
    (shortCheckPk_sound _ 10 15 _ _ e24pTW_check1)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e24pTW_labels :
    (OctadDense.octChunkTerms e24pTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e24pPlanW_word : planWord e24pPlanW = e24pW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e24pPlanW_ok : planOk e24pPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e24pW_growth : tensorWordGrowthAll e24pW = 524288 := by decide +kernel

/-- The tensor bound of `e24pW v`. -/
theorem e24pXW_bnd : TBnd 64 (524288 * (2 ^ 8 - 1)) e24pXW := by
  have h := (tensorPlanS_actual e24pPlanW e24pPlanW_ok (sixthSXF_bndF (w := 64) (by norm_num))
    (by rw [e24pPlanW_word, e24pW_growth]; norm_num) 32).1
  rw [e24pPlanW_word, e24pW_growth] at h
  exact h

/-- The coordinates of `e24pW v`. -/
theorem e24pVW_actual : griessConwayEncode (rhoLocal (identWordLocal e24pW)
    (generatedAxisGlobalTwelveRepresentative 5)) = e24pVW.real := by
  have hT := (tensorPlanS_actual e24pPlanW e24pPlanW_ok (sixthSXF_bndF (w := 64) (by norm_num))
    (by rw [e24pPlanW_word, e24pW_growth]; norm_num) 32).2
  rw [e24pPlanW_word] at hT
  exact IdentVec.word_actual (sixthSrcVecF 64) e24pWW e24pWW_check e24pDW e24pDW_ok e24pDW_cols
    e24pDW_rows _ e24pTW_check _ hT _ (sixthSrcF_rep (by norm_num))

/-- The short block of `e24pW v` satisfies the range conditions. -/
theorem e24pVW_ok : e24pVW.sh.ok = true := ofList_ok _ e24pTW_labels

/-- The short block of `e24pW v` in chunk form. -/
theorem e24pVW_sh : e24pVW.sh = ShortData.ofList (OctadDense.octChunkTerms e24pTW) := rfl

/-- The tensor block of `e24pW v`. -/
theorem e24pVW_ten : e24pVW.ten = tensorRat 64 e24pXW e24pEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
