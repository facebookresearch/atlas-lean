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

/-! # Dense identification data checks: the image of the Eighth source under `e35P`

The representation `e35VP` of `e35P v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e35TP` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e35PlanP` on the literal source tensor (`tensorPlanS_actual`); its binding
`e35VP_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e35P v₈`. -/
def e35XP : List SVec := tensorPlanS 64 e35PlanP e8SrcTenLit

/-- The tensor scale of `e35P v₈`. -/
def e35EP : ℚ := (tensorWordDenAll e35P : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e35P v₈`. -/
def e35VP : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e35P, ShortData.ofList (OctadDense.octChunkTerms e35TP),
    e8SrcVecS.sden, tensorRat 64 e35XP e35EP⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e35P` are certified. -/
theorem e35WP_check : e35WP.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e35DP_ok : e35DP.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e35DP_cols : ∀ i : Fin 24, qmWordP (e35WP.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e35DP.colsP i.val, e35DP.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e35DP_rows : ∀ i : Fin 24,
    fld 24 e35DP.rowsP i.val = rowsOf (fun j => fld 24 e35DP.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e35TP_checkP :
    shortCheckPk e35DP 10 1 e8PS (OctadDense.octChunkTerms e35TPP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e35TP_checkO :
    shortCheckPk e35DP 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e35TPO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e35TP_checkD :
    shortCheckPk e35DP 10 26 e8OddS (OctadDense.octChunkTerms e35TPD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e35TP_check :
    shortCheckF e35DP e8SrcVecS.sh.flat (OctadDense.octChunkTerms e35TP) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e35TP,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e35TP_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e35TP_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e35TP_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e35TP_labels :
    (OctadDense.octChunkTerms e35TP).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e35PlanP_word : planWord e35PlanP = e35P := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e35PlanP_ok : planOk e35PlanP = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e35P_growth : tensorWordGrowthAll e35P = 134217728 := by decide +kernel

/-- The tensor bound of `e35P v₈`. -/
theorem e35XP_bnd : TBnd 64 (134217728 * 10496) e35XP := by
  have h := (tensorPlanS_actual e35PlanP e35PlanP_ok e8SrcTen_tight
    (by rw [e35PlanP_word, e35P_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e35PlanP_word, e35P_growth] at h
  exact h

/-- The coordinates of `e35P v₈`. -/
theorem e35VP_actual : griessConwayEncode (rhoLocal (identWordLocal e35P)
    (generatedAxisGlobalTwelveRepresentative 7)) = e35VP.real := by
  have hT := (tensorPlanS_actual e35PlanP e35PlanP_ok e8SrcTen_tight
    (by rw [e35PlanP_word, e35P_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e35PlanP_word] at hT
  exact IdentVec.word_actual e8SrcVecS e35WP e35WP_check e35DP e35DP_ok e35DP_cols
    e35DP_rows _ e35TP_check _ hT _ e8SrcS_rep

/-- The short block of `e35P v₈` satisfies the range conditions. -/
theorem e35VP_ok : e35VP.sh.ok = true := ofList_ok _ e35TP_labels

/-- The short block of `e35P v₈` in chunk form. -/
theorem e35VP_sh : e35VP.sh = ShortData.ofList (OctadDense.octChunkTerms e35TP) := rfl

/-- The tensor block of `e35P v₈`. -/
theorem e35VP_ten : e35VP.ten = tensorRat 64 e35XP e35EP := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
