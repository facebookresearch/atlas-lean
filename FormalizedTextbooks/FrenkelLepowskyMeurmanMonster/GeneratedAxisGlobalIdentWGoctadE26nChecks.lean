/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26nChecksL

/-! # Factory checks (target side) of the identification Eighth[37]- <-> Seventh[1]+ (record
goctad:E26-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGoctadE26nG_check : wGoctadE26nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGoctadE26nGD_cols : ∀ i : Fin 24, qmWordP (wGoctadE26nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGoctadE26nGD.colsP i.val, wGoctadE26nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGoctadE26nGD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE26nGD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE26nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGoctadE26nGT_check : shortCheckF wGoctadE26nGD seventhShS.flat wGoctadE26nGT = true :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wGoctadE26nW_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE26nG)
    (generatedAxisGlobalTwelveRepresentative 6)) = wGoctadE26nW.real := by
  have hT := (tensorPlanF_actual wGoctadE26nGPlan wGoctadE26nGPlan_ok (srcSeventhX0F_bnd (w := 64)
      (by norm_num))
    (by rw [wGoctadE26nGPlan_word, wGoctadE26nG_growth]; norm_num) srcSeventhD0).2
  rw [wGoctadE26nGPlan_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 64) wGoctadE26nGW wGoctadE26nG_check wGoctadE26nGD
      wGoctadE26nD_ok.2 wGoctadE26nGD_cols
    wGoctadE26nGD_rows wGoctadE26nGT wGoctadE26nGT_check _ hT _ (seventhSrcS_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
