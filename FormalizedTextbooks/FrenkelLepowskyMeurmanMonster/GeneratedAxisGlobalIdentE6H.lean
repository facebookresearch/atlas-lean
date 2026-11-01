/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e6H`

The representation `e6VH` of `e6H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e6TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e6PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e6VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e6H v₈`. -/
def e6XH : List SVec := tensorPlanS 64 e6PlanH e8SrcTenLit

/-- The tensor scale of `e6H v₈`. -/
def e6EH : ℚ := (tensorWordDenAll e6H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e6H v₈`. -/
def e6VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e6H, ShortData.ofList (OctadDense.octChunkTerms e6TH),
    e8SrcVecS.sden, tensorRat 64 e6XH e6EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e6H` are certified. -/
theorem e6WH_check : e6WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e6DH_ok : e6DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e6DH_cols : ∀ i : Fin 24, qmWordP (e6WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e6DH.colsP i.val, e6DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e6DH_rows : ∀ i : Fin 24,
    fld 24 e6DH.rowsP i.val = rowsOf (fun j => fld 24 e6DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e6TH_checkP :
    shortCheckPk e6DH 10 1 e8PS (OctadDense.octChunkTerms e6THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e6TH_checkO :
    shortCheckPk e6DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e6THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e6TH_checkD :
    shortCheckPk e6DH 10 26 e8OddS (OctadDense.octChunkTerms e6THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e6TH_check :
    shortCheckF e6DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e6TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e6TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e6TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e6TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e6TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e6TH_labels :
    (OctadDense.octChunkTerms e6TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e6PlanH_word : planWord e6PlanH = e6H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e6PlanH_ok : planOk e6PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e6H_growth : tensorWordGrowthAll e6H = 65536 := by decide +kernel

/-- The tensor bound of `e6H v₈`. -/
theorem e6XH_bnd : TBnd 64 (65536 * 10496) e6XH := by
  have h := (tensorPlanS_actual e6PlanH e6PlanH_ok e8SrcTen_tight
    (by rw [e6PlanH_word, e6H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e6PlanH_word, e6H_growth] at h
  exact h

/-- The coordinates of `e6H v₈`. -/
theorem e6VH_actual : griessConwayEncode (rhoLocal (identWordLocal e6H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e6VH.real := by
  have hT := (tensorPlanS_actual e6PlanH e6PlanH_ok e8SrcTen_tight
    (by rw [e6PlanH_word, e6H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e6PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e6WH e6WH_check e6DH e6DH_ok e6DH_cols
    e6DH_rows _ e6TH_check _ hT _ e8SrcS_rep

/-- The short block of `e6H v₈` satisfies the range conditions. -/
theorem e6VH_ok : e6VH.sh.ok = true := ofList_ok _ e6TH_labels

/-- The short block of `e6H v₈` in chunk form. -/
theorem e6VH_sh : e6VH.sh = ShortData.ofList (OctadDense.octChunkTerms e6TH) := rfl

/-- The tensor block of `e6H v₈`. -/
theorem e6VH_ten : e6VH.ten = tensorRat 64 e6XH e6EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
