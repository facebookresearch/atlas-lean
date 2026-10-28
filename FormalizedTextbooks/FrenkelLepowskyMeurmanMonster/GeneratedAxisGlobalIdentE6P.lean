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

/-! # Dense identification data checks: the image of the Eighth source under `e6P`

The representation `e6VP` of `e6P v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e6TP` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e6PlanP` on the literal source tensor (`tensorPlanS_actual`); its binding
`e6VP_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e6P v₈`. -/
def e6XP : List SVec := tensorPlanS 64 e6PlanP e8SrcTenLit

/-- The tensor scale of `e6P v₈`. -/
def e6EP : ℚ := (tensorWordDenAll e6P : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e6P v₈`. -/
def e6VP : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e6P, ShortData.ofList (OctadDense.octChunkTerms e6TP),
    e8SrcVecS.sden, tensorRat 64 e6XP e6EP⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e6P` are certified. -/
theorem e6WP_check : e6WP.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e6DP_ok : e6DP.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e6DP_cols : ∀ i : Fin 24, qmWordP (e6WP.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e6DP.colsP i.val, e6DP.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e6DP_rows : ∀ i : Fin 24,
    fld 24 e6DP.rowsP i.val = rowsOf (fun j => fld 24 e6DP.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e6TP_checkP :
    shortCheckPk e6DP 10 1 e8PS (OctadDense.octChunkTerms e6TPP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e6TP_checkO :
    shortCheckPk e6DP 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e6TPO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e6TP_checkD :
    shortCheckPk e6DP 10 26 e8OddS (OctadDense.octChunkTerms e6TPD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e6TP_check :
    shortCheckF e6DP e8SrcVecS.sh.flat (OctadDense.octChunkTerms e6TP) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e6TP,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e6TP_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e6TP_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e6TP_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e6TP_labels :
    (OctadDense.octChunkTerms e6TP).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e6PlanP_word : planWord e6PlanP = e6P := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e6PlanP_ok : planOk e6PlanP = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e6P_growth : tensorWordGrowthAll e6P = 524288 := by decide +kernel

/-- The tensor bound of `e6P v₈`. -/
theorem e6XP_bnd : TBnd 64 (524288 * 10496) e6XP := by
  have h := (tensorPlanS_actual e6PlanP e6PlanP_ok e8SrcTen_tight
    (by rw [e6PlanP_word, e6P_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e6PlanP_word, e6P_growth] at h
  exact h

/-- The coordinates of `e6P v₈`. -/
theorem e6VP_actual : griessConwayEncode (rhoLocal (identWordLocal e6P)
    (generatedAxisGlobalTwelveRepresentative 7)) = e6VP.real := by
  have hT := (tensorPlanS_actual e6PlanP e6PlanP_ok e8SrcTen_tight
    (by rw [e6PlanP_word, e6P_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e6PlanP_word] at hT
  exact IdentVec.word_actual e8SrcVecS e6WP e6WP_check e6DP e6DP_ok e6DP_cols
    e6DP_rows _ e6TP_check _ hT _ e8SrcS_rep

/-- The short block of `e6P v₈` satisfies the range conditions. -/
theorem e6VP_ok : e6VP.sh.ok = true := ofList_ok _ e6TP_labels

/-- The short block of `e6P v₈` in chunk form. -/
theorem e6VP_sh : e6VP.sh = ShortData.ofList (OctadDense.octChunkTerms e6TP) := rfl

/-- The tensor block of `e6P v₈`. -/
theorem e6VP_ten : e6VP.ten = tensorRat 64 e6XP e6EP := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
