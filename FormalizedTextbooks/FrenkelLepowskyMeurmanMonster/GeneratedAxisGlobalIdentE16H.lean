/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e16H`

The representation `e16VH` of `e16H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e16TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e16PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e16VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e16H v₈`. -/
def e16XH : List SVec := tensorPlanS 64 e16PlanH e8SrcTenLit

/-- The tensor scale of `e16H v₈`. -/
def e16EH : ℚ := (tensorWordDenAll e16H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e16H v₈`. -/
def e16VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e16H, ShortData.ofList (OctadDense.octChunkTerms e16TH),
    e8SrcVecS.sden, tensorRat 64 e16XH e16EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e16H` are certified. -/
theorem e16WH_check : e16WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e16DH_ok : e16DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e16DH_cols : ∀ i : Fin 24, qmWordP (e16WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e16DH.colsP i.val, e16DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e16DH_rows : ∀ i : Fin 24,
    fld 24 e16DH.rowsP i.val = rowsOf (fun j => fld 24 e16DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e16TH_checkP :
    shortCheckPk e16DH 10 1 e8PS (OctadDense.octChunkTerms e16THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e16TH_checkO :
    shortCheckPk e16DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e16THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e16TH_checkD :
    shortCheckPk e16DH 10 26 e8OddS (OctadDense.octChunkTerms e16THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e16TH_check :
    shortCheckF e16DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e16TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e16TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e16TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e16TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e16TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e16TH_labels :
    (OctadDense.octChunkTerms e16TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e16PlanH_word : planWord e16PlanH = e16H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e16PlanH_ok : planOk e16PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e16H_growth : tensorWordGrowthAll e16H = 65536 := by decide +kernel

/-- The tensor bound of `e16H v₈`. -/
theorem e16XH_bnd : TBnd 64 (65536 * 10496) e16XH := by
  have h := (tensorPlanS_actual e16PlanH e16PlanH_ok e8SrcTen_tight
    (by rw [e16PlanH_word, e16H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e16PlanH_word, e16H_growth] at h
  exact h

/-- The coordinates of `e16H v₈`. -/
theorem e16VH_actual : griessConwayEncode (rhoLocal (identWordLocal e16H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e16VH.real := by
  have hT := (tensorPlanS_actual e16PlanH e16PlanH_ok e8SrcTen_tight
    (by rw [e16PlanH_word, e16H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e16PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e16WH e16WH_check e16DH e16DH_ok e16DH_cols
    e16DH_rows _ e16TH_check _ hT _ e8SrcS_rep

/-- The short block of `e16H v₈` satisfies the range conditions. -/
theorem e16VH_ok : e16VH.sh.ok = true := ofList_ok _ e16TH_labels

/-- The short block of `e16H v₈` in chunk form. -/
theorem e16VH_sh : e16VH.sh = ShortData.ofList (OctadDense.octChunkTerms e16TH) := rfl

/-- The tensor block of `e16H v₈`. -/
theorem e16VH_ten : e16VH.ten = tensorRat 64 e16XH e16EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
