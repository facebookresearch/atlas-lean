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

/-! # Dense identification data checks: the image of the Eighth source under `e28H`

The representation `e28VH` of `e28H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e28TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e28PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e28VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e28H v₈`. -/
def e28XH : List SVec := tensorPlanS 64 e28PlanH e8SrcTenLit

/-- The tensor scale of `e28H v₈`. -/
def e28EH : ℚ := (tensorWordDenAll e28H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e28H v₈`. -/
def e28VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e28H, ShortData.ofList (OctadDense.octChunkTerms e28TH),
    e8SrcVecS.sden, tensorRat 64 e28XH e28EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e28H` are certified. -/
theorem e28WH_check : e28WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e28DH_ok : e28DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e28DH_cols : ∀ i : Fin 24, qmWordP (e28WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e28DH.colsP i.val, e28DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e28DH_rows : ∀ i : Fin 24,
    fld 24 e28DH.rowsP i.val = rowsOf (fun j => fld 24 e28DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e28TH_checkP :
    shortCheckPk e28DH 10 1 e8PS (OctadDense.octChunkTerms e28THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e28TH_checkO :
    shortCheckPk e28DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e28THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e28TH_checkD :
    shortCheckPk e28DH 10 26 e8OddS (OctadDense.octChunkTerms e28THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e28TH_check :
    shortCheckF e28DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e28TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e28TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e28TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e28TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e28TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e28TH_labels :
    (OctadDense.octChunkTerms e28TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e28PlanH_word : planWord e28PlanH = e28H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e28PlanH_ok : planOk e28PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e28H_growth : tensorWordGrowthAll e28H = 256 := by decide +kernel

/-- The tensor bound of `e28H v₈`. -/
theorem e28XH_bnd : TBnd 64 (256 * 10496) e28XH := by
  have h := (tensorPlanS_actual e28PlanH e28PlanH_ok e8SrcTen_tight
    (by rw [e28PlanH_word, e28H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e28PlanH_word, e28H_growth] at h
  exact h

/-- The coordinates of `e28H v₈`. -/
theorem e28VH_actual : griessConwayEncode (rhoLocal (identWordLocal e28H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e28VH.real := by
  have hT := (tensorPlanS_actual e28PlanH e28PlanH_ok e8SrcTen_tight
    (by rw [e28PlanH_word, e28H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e28PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e28WH e28WH_check e28DH e28DH_ok e28DH_cols
    e28DH_rows _ e28TH_check _ hT _ e8SrcS_rep

/-- The short block of `e28H v₈` satisfies the range conditions. -/
theorem e28VH_ok : e28VH.sh.ok = true := ofList_ok _ e28TH_labels

/-- The short block of `e28H v₈` in chunk form. -/
theorem e28VH_sh : e28VH.sh = ShortData.ofList (OctadDense.octChunkTerms e28TH) := rfl

/-- The tensor block of `e28H v₈`. -/
theorem e28VH_ten : e28VH.ten = tensorRat 64 e28XH e28EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
