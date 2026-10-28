/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE28Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck

/-! # Dense identification data checks: the image of the Eighth source under `e28Gm`

The representation `e28VGm` of `e28Gm v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e28TGm` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e28PlanGm` on the literal source tensor (`tensorPlanS_actual`); its binding
`e28VGm_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e28Gm v₈`. -/
def e28XGm : List SVec := tensorPlanS 64 e28PlanGm e8SrcTenLit

/-- The tensor scale of `e28Gm v₈`. -/
def e28EGm : ℚ := (tensorWordDenAll e28Gm : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e28Gm v₈`. -/
def e28VGm : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e28Gm, ShortData.ofList (OctadDense.octChunkTerms e28TGm),
    e8SrcVecS.sden, tensorRat 64 e28XGm e28EGm⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e28Gm` are certified. -/
theorem e28WGm_check : e28WGm.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e28DGm_ok : e28DGm.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e28DGm_cols : ∀ i : Fin 24, qmWordP (e28WGm.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e28DGm.colsP i.val, e28DGm.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e28DGm_rows : ∀ i : Fin 24,
    fld 24 e28DGm.rowsP i.val = rowsOf (fun j => fld 24 e28DGm.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e28TGm_checkP :
    shortCheckPk e28DGm 10 1 e8PS (OctadDense.octChunkTerms e28TGmP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e28TGm_checkO :
    shortCheckPk e28DGm 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e28TGmO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e28TGm_checkD :
    shortCheckPk e28DGm 10 26 e8OddS (OctadDense.octChunkTerms e28TGmD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e28TGm_check :
    shortCheckF e28DGm e8SrcVecS.sh.flat (OctadDense.octChunkTerms e28TGm) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e28TGm,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e28TGm_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e28TGm_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e28TGm_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e28TGm_labels :
    (OctadDense.octChunkTerms e28TGm).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e28PlanGm_word : planWord e28PlanGm = e28Gm := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e28PlanGm_ok : planOk e28PlanGm = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e28Gm_growth : tensorWordGrowthAll e28Gm = 2048 := by decide +kernel

/-- The tensor bound of `e28Gm v₈`. -/
theorem e28XGm_bnd : TBnd 64 (2048 * 10496) e28XGm := by
  have h := (tensorPlanS_actual e28PlanGm e28PlanGm_ok e8SrcTen_tight
    (by rw [e28PlanGm_word, e28Gm_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e28PlanGm_word, e28Gm_growth] at h
  exact h

/-- The coordinates of `e28Gm v₈`. -/
theorem e28VGm_actual : griessConwayEncode (rhoLocal (identWordLocal e28Gm)
    (generatedAxisGlobalTwelveRepresentative 7)) = e28VGm.real := by
  have hT := (tensorPlanS_actual e28PlanGm e28PlanGm_ok e8SrcTen_tight
    (by rw [e28PlanGm_word, e28Gm_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e28PlanGm_word] at hT
  exact IdentVec.word_actual e8SrcVecS e28WGm e28WGm_check e28DGm e28DGm_ok e28DGm_cols
    e28DGm_rows _ e28TGm_check _ hT _ e8SrcS_rep

/-- The short block of `e28Gm v₈` satisfies the range conditions. -/
theorem e28VGm_ok : e28VGm.sh.ok = true := ofList_ok _ e28TGm_labels

/-- The short block of `e28Gm v₈` in chunk form. -/
theorem e28VGm_sh : e28VGm.sh = ShortData.ofList (OctadDense.octChunkTerms e28TGm) := rfl

/-- The tensor block of `e28Gm v₈`. -/
theorem e28VGm_ten : e28VGm.ten = tensorRat 64 e28XGm e28EGm := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
