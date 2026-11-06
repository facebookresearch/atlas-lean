/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e3H`

The representation `e3VH` of `e3H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e3TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e3PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e3VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e3H v₈`. -/
def e3XH : List SVec := tensorPlanS 64 e3PlanH e8SrcTenLit

/-- The tensor scale of `e3H v₈`. -/
def e3EH : ℚ := (tensorWordDenAll e3H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e3H v₈`. -/
def e3VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e3H, ShortData.ofList (OctadDense.octChunkTerms e3TH),
    e8SrcVecS.sden, tensorRat 64 e3XH e3EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e3H` are certified. -/
theorem e3WH_check : e3WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e3DH_ok : e3DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e3DH_cols : ∀ i : Fin 24, qmWordP (e3WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e3DH.colsP i.val, e3DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e3DH_rows : ∀ i : Fin 24,
    fld 24 e3DH.rowsP i.val = rowsOf (fun j => fld 24 e3DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e3TH_checkP :
    shortCheckPk e3DH 10 1 e8PS (OctadDense.octChunkTerms e3THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e3TH_checkO :
    shortCheckPk e3DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e3THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e3TH_checkD :
    shortCheckPk e3DH 10 26 e8OddS (OctadDense.octChunkTerms e3THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e3TH_check :
    shortCheckF e3DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e3TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e3TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e3TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e3TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e3TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e3TH_labels :
    (OctadDense.octChunkTerms e3TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e3PlanH_word : planWord e3PlanH = e3H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e3PlanH_ok : planOk e3PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e3H_growth : tensorWordGrowthAll e3H = 65536 := by decide +kernel

/-- The tensor bound of `e3H v₈`. -/
theorem e3XH_bnd : TBnd 64 (65536 * 10496) e3XH := by
  have h := (tensorPlanS_actual e3PlanH e3PlanH_ok e8SrcTen_tight
    (by rw [e3PlanH_word, e3H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e3PlanH_word, e3H_growth] at h
  exact h

/-- The coordinates of `e3H v₈`. -/
theorem e3VH_actual : griessConwayEncode (rhoLocal (identWordLocal e3H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e3VH.real := by
  have hT := (tensorPlanS_actual e3PlanH e3PlanH_ok e8SrcTen_tight
    (by rw [e3PlanH_word, e3H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e3PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e3WH e3WH_check e3DH e3DH_ok e3DH_cols
    e3DH_rows _ e3TH_check _ hT _ e8SrcS_rep

/-- The short block of `e3H v₈` satisfies the range conditions. -/
theorem e3VH_ok : e3VH.sh.ok = true := ofList_ok _ e3TH_labels

/-- The short block of `e3H v₈` in chunk form. -/
theorem e3VH_sh : e3VH.sh = ShortData.ofList (OctadDense.octChunkTerms e3TH) := rfl

/-- The tensor block of `e3H v₈`. -/
theorem e3VH_ten : e3VH.ten = tensorRat 64 e3XH e3EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
