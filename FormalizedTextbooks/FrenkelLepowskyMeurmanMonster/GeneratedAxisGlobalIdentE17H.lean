/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e17H`

The representation `e17VH` of `e17H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e17TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e17PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e17VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e17H v₈`. -/
def e17XH : List SVec := tensorPlanS 64 e17PlanH e8SrcTenLit

/-- The tensor scale of `e17H v₈`. -/
def e17EH : ℚ := (tensorWordDenAll e17H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e17H v₈`. -/
def e17VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e17H, ShortData.ofList (OctadDense.octChunkTerms e17TH),
    e8SrcVecS.sden, tensorRat 64 e17XH e17EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e17H` are certified. -/
theorem e17WH_check : e17WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e17DH_ok : e17DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e17DH_cols : ∀ i : Fin 24, qmWordP (e17WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e17DH.colsP i.val, e17DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e17DH_rows : ∀ i : Fin 24,
    fld 24 e17DH.rowsP i.val = rowsOf (fun j => fld 24 e17DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e17TH_checkP :
    shortCheckPk e17DH 10 1 e8PS (OctadDense.octChunkTerms e17THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e17TH_checkO :
    shortCheckPk e17DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e17THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e17TH_checkD :
    shortCheckPk e17DH 10 26 e8OddS (OctadDense.octChunkTerms e17THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e17TH_check :
    shortCheckF e17DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e17TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e17TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e17TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e17TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e17TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e17TH_labels :
    (OctadDense.octChunkTerms e17TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e17PlanH_word : planWord e17PlanH = e17H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e17PlanH_ok : planOk e17PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e17H_growth : tensorWordGrowthAll e17H = 65536 := by decide +kernel

/-- The tensor bound of `e17H v₈`. -/
theorem e17XH_bnd : TBnd 64 (65536 * 10496) e17XH := by
  have h := (tensorPlanS_actual e17PlanH e17PlanH_ok e8SrcTen_tight
    (by rw [e17PlanH_word, e17H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e17PlanH_word, e17H_growth] at h
  exact h

/-- The coordinates of `e17H v₈`. -/
theorem e17VH_actual : griessConwayEncode (rhoLocal (identWordLocal e17H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e17VH.real := by
  have hT := (tensorPlanS_actual e17PlanH e17PlanH_ok e8SrcTen_tight
    (by rw [e17PlanH_word, e17H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e17PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e17WH e17WH_check e17DH e17DH_ok e17DH_cols
    e17DH_rows _ e17TH_check _ hT _ e8SrcS_rep

/-- The short block of `e17H v₈` satisfies the range conditions. -/
theorem e17VH_ok : e17VH.sh.ok = true := ofList_ok _ e17TH_labels

/-- The short block of `e17H v₈` in chunk form. -/
theorem e17VH_sh : e17VH.sh = ShortData.ofList (OctadDense.octChunkTerms e17TH) := rfl

/-- The tensor block of `e17H v₈`. -/
theorem e17VH_ten : e17VH.ten = tensorRat 64 e17XH e17EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
