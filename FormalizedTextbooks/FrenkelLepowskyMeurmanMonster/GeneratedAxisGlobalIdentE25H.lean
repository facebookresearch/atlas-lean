/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e25H`

The representation `e25VH` of `e25H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e25TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e25PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e25VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e25H v₈`. -/
def e25XH : List SVec := tensorPlanS 64 e25PlanH e8SrcTenLit

/-- The tensor scale of `e25H v₈`. -/
def e25EH : ℚ := (tensorWordDenAll e25H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e25H v₈`. -/
def e25VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e25H, ShortData.ofList (OctadDense.octChunkTerms e25TH),
    e8SrcVecS.sden, tensorRat 64 e25XH e25EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e25H` are certified. -/
theorem e25WH_check : e25WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e25DH_ok : e25DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e25DH_cols : ∀ i : Fin 24, qmWordP (e25WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e25DH.colsP i.val, e25DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e25DH_rows : ∀ i : Fin 24,
    fld 24 e25DH.rowsP i.val = rowsOf (fun j => fld 24 e25DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e25TH_checkP :
    shortCheckPk e25DH 10 1 e8PS (OctadDense.octChunkTerms e25THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e25TH_checkO :
    shortCheckPk e25DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e25THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e25TH_checkD :
    shortCheckPk e25DH 10 26 e8OddS (OctadDense.octChunkTerms e25THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e25TH_check :
    shortCheckF e25DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e25TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e25TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e25TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e25TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e25TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e25TH_labels :
    (OctadDense.octChunkTerms e25TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e25PlanH_word : planWord e25PlanH = e25H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e25PlanH_ok : planOk e25PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e25H_growth : tensorWordGrowthAll e25H = 256 := by decide +kernel

/-- The tensor bound of `e25H v₈`. -/
theorem e25XH_bnd : TBnd 64 (256 * 10496) e25XH := by
  have h := (tensorPlanS_actual e25PlanH e25PlanH_ok e8SrcTen_tight
    (by rw [e25PlanH_word, e25H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e25PlanH_word, e25H_growth] at h
  exact h

/-- The coordinates of `e25H v₈`. -/
theorem e25VH_actual : griessConwayEncode (rhoLocal (identWordLocal e25H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e25VH.real := by
  have hT := (tensorPlanS_actual e25PlanH e25PlanH_ok e8SrcTen_tight
    (by rw [e25PlanH_word, e25H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e25PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e25WH e25WH_check e25DH e25DH_ok e25DH_cols
    e25DH_rows _ e25TH_check _ hT _ e8SrcS_rep

/-- The short block of `e25H v₈` satisfies the range conditions. -/
theorem e25VH_ok : e25VH.sh.ok = true := ofList_ok _ e25TH_labels

/-- The short block of `e25H v₈` in chunk form. -/
theorem e25VH_sh : e25VH.sh = ShortData.ofList (OctadDense.octChunkTerms e25TH) := rfl

/-- The tensor block of `e25H v₈`. -/
theorem e25VH_ten : e25VH.ten = tensorRat 64 e25XH e25EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
