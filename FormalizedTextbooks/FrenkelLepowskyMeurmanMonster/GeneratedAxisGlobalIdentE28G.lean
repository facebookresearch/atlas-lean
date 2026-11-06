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

/-! # Dense identification data checks: the image of the Eighth source under `e28G`

The representation `e28VG` of `e28G v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e28TG` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e28PlanG` on the literal source tensor (`tensorPlanS_actual`); its binding
`e28VG_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e28G v₈`. -/
def e28XG : List SVec := tensorPlanS 64 e28PlanG e8SrcTenLit

/-- The tensor scale of `e28G v₈`. -/
def e28EG : ℚ := (tensorWordDenAll e28G : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e28G v₈`. -/
def e28VG : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e28G, ShortData.ofList (OctadDense.octChunkTerms e28TG),
    e8SrcVecS.sden, tensorRat 64 e28XG e28EG⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e28G` are certified. -/
theorem e28WG_check : e28WG.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e28DG_ok : e28DG.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e28DG_cols : ∀ i : Fin 24, qmWordP (e28WG.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e28DG.colsP i.val, e28DG.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e28DG_rows : ∀ i : Fin 24,
    fld 24 e28DG.rowsP i.val = rowsOf (fun j => fld 24 e28DG.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e28TG_checkP :
    shortCheckPk e28DG 10 1 e8PS (OctadDense.octChunkTerms e28TGP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e28TG_checkO :
    shortCheckPk e28DG 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e28TGO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e28TG_checkD :
    shortCheckPk e28DG 10 26 e8OddS (OctadDense.octChunkTerms e28TGD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e28TG_check :
    shortCheckF e28DG e8SrcVecS.sh.flat (OctadDense.octChunkTerms e28TG) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e28TG,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e28TG_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e28TG_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e28TG_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e28TG_labels :
    (OctadDense.octChunkTerms e28TG).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e28PlanG_word : planWord e28PlanG = e28G := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e28PlanG_ok : planOk e28PlanG = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e28G_growth : tensorWordGrowthAll e28G = 2048 := by decide +kernel

/-- The tensor bound of `e28G v₈`. -/
theorem e28XG_bnd : TBnd 64 (2048 * 10496) e28XG := by
  have h := (tensorPlanS_actual e28PlanG e28PlanG_ok e8SrcTen_tight
    (by rw [e28PlanG_word, e28G_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e28PlanG_word, e28G_growth] at h
  exact h

/-- The coordinates of `e28G v₈`. -/
theorem e28VG_actual : griessConwayEncode (rhoLocal (identWordLocal e28G)
    (generatedAxisGlobalTwelveRepresentative 7)) = e28VG.real := by
  have hT := (tensorPlanS_actual e28PlanG e28PlanG_ok e8SrcTen_tight
    (by rw [e28PlanG_word, e28G_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e28PlanG_word] at hT
  exact IdentVec.word_actual e8SrcVecS e28WG e28WG_check e28DG e28DG_ok e28DG_cols
    e28DG_rows _ e28TG_check _ hT _ e8SrcS_rep

/-- The short block of `e28G v₈` satisfies the range conditions. -/
theorem e28VG_ok : e28VG.sh.ok = true := ofList_ok _ e28TG_labels

/-- The short block of `e28G v₈` in chunk form. -/
theorem e28VG_sh : e28VG.sh = ShortData.ofList (OctadDense.octChunkTerms e28TG) := rfl

/-- The tensor block of `e28G v₈`. -/
theorem e28VG_ten : e28VG.ten = tensorRat 64 e28XG e28EG := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
