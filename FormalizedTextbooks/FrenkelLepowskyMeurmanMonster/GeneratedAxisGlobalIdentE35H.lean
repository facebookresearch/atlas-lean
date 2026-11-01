/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e35H`

The representation `e35VH` of `e35H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e35TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e35PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e35VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e35H v₈`. -/
def e35XH : List SVec := tensorPlanS 64 e35PlanH e8SrcTenLit

/-- The tensor scale of `e35H v₈`. -/
def e35EH : ℚ := (tensorWordDenAll e35H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e35H v₈`. -/
def e35VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e35H, ShortData.ofList (OctadDense.octChunkTerms e35TH),
    e8SrcVecS.sden, tensorRat 64 e35XH e35EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e35H` are certified. -/
theorem e35WH_check : e35WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e35DH_ok : e35DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e35DH_cols : ∀ i : Fin 24, qmWordP (e35WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e35DH.colsP i.val, e35DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e35DH_rows : ∀ i : Fin 24,
    fld 24 e35DH.rowsP i.val = rowsOf (fun j => fld 24 e35DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e35TH_checkP :
    shortCheckPk e35DH 10 1 e8PS (OctadDense.octChunkTerms e35THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e35TH_checkO :
    shortCheckPk e35DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e35THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e35TH_checkD :
    shortCheckPk e35DH 10 26 e8OddS (OctadDense.octChunkTerms e35THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e35TH_check :
    shortCheckF e35DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e35TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e35TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e35TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e35TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e35TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e35TH_labels :
    (OctadDense.octChunkTerms e35TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e35PlanH_word : planWord e35PlanH = e35H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e35PlanH_ok : planOk e35PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e35H_growth : tensorWordGrowthAll e35H = 16777216 := by decide +kernel

/-- The tensor bound of `e35H v₈`. -/
theorem e35XH_bnd : TBnd 64 (16777216 * 10496) e35XH := by
  have h := (tensorPlanS_actual e35PlanH e35PlanH_ok e8SrcTen_tight
    (by rw [e35PlanH_word, e35H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e35PlanH_word, e35H_growth] at h
  exact h

/-- The coordinates of `e35H v₈`. -/
theorem e35VH_actual : griessConwayEncode (rhoLocal (identWordLocal e35H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e35VH.real := by
  have hT := (tensorPlanS_actual e35PlanH e35PlanH_ok e8SrcTen_tight
    (by rw [e35PlanH_word, e35H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e35PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e35WH e35WH_check e35DH e35DH_ok e35DH_cols
    e35DH_rows _ e35TH_check _ hT _ e8SrcS_rep

/-- The short block of `e35H v₈` satisfies the range conditions. -/
theorem e35VH_ok : e35VH.sh.ok = true := ofList_ok _ e35TH_labels

/-- The short block of `e35H v₈` in chunk form. -/
theorem e35VH_sh : e35VH.sh = ShortData.ofList (OctadDense.octChunkTerms e35TH) := rfl

/-- The tensor block of `e35H v₈`. -/
theorem e35VH_ten : e35VH.ten = tensorRat 64 e35XH e35EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
