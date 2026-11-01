/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e23H`

The representation `e23VH` of `e23H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e23TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e23PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e23VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e23H v₈`. -/
def e23XH : List SVec := tensorPlanS 64 e23PlanH e8SrcTenLit

/-- The tensor scale of `e23H v₈`. -/
def e23EH : ℚ := (tensorWordDenAll e23H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e23H v₈`. -/
def e23VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e23H, ShortData.ofList (OctadDense.octChunkTerms e23TH),
    e8SrcVecS.sden, tensorRat 64 e23XH e23EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e23H` are certified. -/
theorem e23WH_check : e23WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e23DH_ok : e23DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e23DH_cols : ∀ i : Fin 24, qmWordP (e23WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e23DH.colsP i.val, e23DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e23DH_rows : ∀ i : Fin 24,
    fld 24 e23DH.rowsP i.val = rowsOf (fun j => fld 24 e23DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e23TH_checkP :
    shortCheckPk e23DH 10 1 e8PS (OctadDense.octChunkTerms e23THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e23TH_checkO :
    shortCheckPk e23DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e23THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e23TH_checkD :
    shortCheckPk e23DH 10 26 e8OddS (OctadDense.octChunkTerms e23THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e23TH_check :
    shortCheckF e23DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e23TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e23TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e23TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e23TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e23TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e23TH_labels :
    (OctadDense.octChunkTerms e23TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e23PlanH_word : planWord e23PlanH = e23H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e23PlanH_ok : planOk e23PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e23H_growth : tensorWordGrowthAll e23H = 65536 := by decide +kernel

/-- The tensor bound of `e23H v₈`. -/
theorem e23XH_bnd : TBnd 64 (65536 * 10496) e23XH := by
  have h := (tensorPlanS_actual e23PlanH e23PlanH_ok e8SrcTen_tight
    (by rw [e23PlanH_word, e23H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e23PlanH_word, e23H_growth] at h
  exact h

/-- The coordinates of `e23H v₈`. -/
theorem e23VH_actual : griessConwayEncode (rhoLocal (identWordLocal e23H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e23VH.real := by
  have hT := (tensorPlanS_actual e23PlanH e23PlanH_ok e8SrcTen_tight
    (by rw [e23PlanH_word, e23H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e23PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e23WH e23WH_check e23DH e23DH_ok e23DH_cols
    e23DH_rows _ e23TH_check _ hT _ e8SrcS_rep

/-- The short block of `e23H v₈` satisfies the range conditions. -/
theorem e23VH_ok : e23VH.sh.ok = true := ofList_ok _ e23TH_labels

/-- The short block of `e23H v₈` in chunk form. -/
theorem e23VH_sh : e23VH.sh = ShortData.ofList (OctadDense.octChunkTerms e23TH) := rfl

/-- The tensor block of `e23H v₈`. -/
theorem e23VH_ten : e23VH.ten = tensorRat 64 e23XH e23EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
