/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e13H`

The representation `e13VH` of `e13H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e13TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e13PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e13VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e13H v₈`. -/
def e13XH : List SVec := tensorPlanS 64 e13PlanH e8SrcTenLit

/-- The tensor scale of `e13H v₈`. -/
def e13EH : ℚ := (tensorWordDenAll e13H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e13H v₈`. -/
def e13VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e13H, ShortData.ofList (OctadDense.octChunkTerms e13TH),
    e8SrcVecS.sden, tensorRat 64 e13XH e13EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e13H` are certified. -/
theorem e13WH_check : e13WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e13DH_ok : e13DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e13DH_cols : ∀ i : Fin 24, qmWordP (e13WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e13DH.colsP i.val, e13DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e13DH_rows : ∀ i : Fin 24,
    fld 24 e13DH.rowsP i.val = rowsOf (fun j => fld 24 e13DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e13TH_checkP :
    shortCheckPk e13DH 10 1 e8PS (OctadDense.octChunkTerms e13THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e13TH_checkO :
    shortCheckPk e13DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e13THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e13TH_checkD :
    shortCheckPk e13DH 10 26 e8OddS (OctadDense.octChunkTerms e13THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e13TH_check :
    shortCheckF e13DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e13TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e13TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e13TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e13TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e13TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e13TH_labels :
    (OctadDense.octChunkTerms e13TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e13PlanH_word : planWord e13PlanH = e13H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e13PlanH_ok : planOk e13PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e13H_growth : tensorWordGrowthAll e13H = 65536 := by decide +kernel

/-- The tensor bound of `e13H v₈`. -/
theorem e13XH_bnd : TBnd 64 (65536 * 10496) e13XH := by
  have h := (tensorPlanS_actual e13PlanH e13PlanH_ok e8SrcTen_tight
    (by rw [e13PlanH_word, e13H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e13PlanH_word, e13H_growth] at h
  exact h

/-- The coordinates of `e13H v₈`. -/
theorem e13VH_actual : griessConwayEncode (rhoLocal (identWordLocal e13H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e13VH.real := by
  have hT := (tensorPlanS_actual e13PlanH e13PlanH_ok e8SrcTen_tight
    (by rw [e13PlanH_word, e13H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e13PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e13WH e13WH_check e13DH e13DH_ok e13DH_cols
    e13DH_rows _ e13TH_check _ hT _ e8SrcS_rep

/-- The short block of `e13H v₈` satisfies the range conditions. -/
theorem e13VH_ok : e13VH.sh.ok = true := ofList_ok _ e13TH_labels

/-- The short block of `e13H v₈` in chunk form. -/
theorem e13VH_sh : e13VH.sh = ShortData.ofList (OctadDense.octChunkTerms e13TH) := rfl

/-- The tensor block of `e13H v₈`. -/
theorem e13VH_ten : e13VH.ten = tensorRat 64 e13XH e13EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
