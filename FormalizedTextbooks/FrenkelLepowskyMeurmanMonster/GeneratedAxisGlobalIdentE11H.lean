/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e11H`

The representation `e11VH` of `e11H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e11TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e11PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e11VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e11H v₈`. -/
def e11XH : List SVec := tensorPlanS 64 e11PlanH e8SrcTenLit

/-- The tensor scale of `e11H v₈`. -/
def e11EH : ℚ := (tensorWordDenAll e11H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e11H v₈`. -/
def e11VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e11H, ShortData.ofList (OctadDense.octChunkTerms e11TH),
    e8SrcVecS.sden, tensorRat 64 e11XH e11EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e11H` are certified. -/
theorem e11WH_check : e11WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e11DH_ok : e11DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e11DH_cols : ∀ i : Fin 24, qmWordP (e11WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e11DH.colsP i.val, e11DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e11DH_rows : ∀ i : Fin 24,
    fld 24 e11DH.rowsP i.val = rowsOf (fun j => fld 24 e11DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e11TH_checkP :
    shortCheckPk e11DH 10 1 e8PS (OctadDense.octChunkTerms e11THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e11TH_checkO :
    shortCheckPk e11DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e11THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e11TH_checkD :
    shortCheckPk e11DH 10 26 e8OddS (OctadDense.octChunkTerms e11THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e11TH_check :
    shortCheckF e11DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e11TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e11TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e11TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e11TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e11TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e11TH_labels :
    (OctadDense.octChunkTerms e11TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e11PlanH_word : planWord e11PlanH = e11H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e11PlanH_ok : planOk e11PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e11H_growth : tensorWordGrowthAll e11H = 16777216 := by decide +kernel

/-- The tensor bound of `e11H v₈`. -/
theorem e11XH_bnd : TBnd 64 (16777216 * 10496) e11XH := by
  have h := (tensorPlanS_actual e11PlanH e11PlanH_ok e8SrcTen_tight
    (by rw [e11PlanH_word, e11H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e11PlanH_word, e11H_growth] at h
  exact h

/-- The coordinates of `e11H v₈`. -/
theorem e11VH_actual : griessConwayEncode (rhoLocal (identWordLocal e11H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e11VH.real := by
  have hT := (tensorPlanS_actual e11PlanH e11PlanH_ok e8SrcTen_tight
    (by rw [e11PlanH_word, e11H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e11PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e11WH e11WH_check e11DH e11DH_ok e11DH_cols
    e11DH_rows _ e11TH_check _ hT _ e8SrcS_rep

/-- The short block of `e11H v₈` satisfies the range conditions. -/
theorem e11VH_ok : e11VH.sh.ok = true := ofList_ok _ e11TH_labels

/-- The short block of `e11H v₈` in chunk form. -/
theorem e11VH_sh : e11VH.sh = ShortData.ofList (OctadDense.octChunkTerms e11TH) := rfl

/-- The tensor block of `e11H v₈`. -/
theorem e11VH_ten : e11VH.ten = tensorRat 64 e11XH e11EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
