/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9pChecksL

/-! # Factory checks (target side) of the identification Eighth[13]+ <-> Seventh[14]+ (record
goctad:E9+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGoctadE9pG_check : wGoctadE9pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGoctadE9pGD_cols : ∀ i : Fin 24, qmWordP (wGoctadE9pGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGoctadE9pGD.colsP i.val, wGoctadE9pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGoctadE9pGD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE9pGD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE9pGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGoctadE9pGT_check : shortCheckF wGoctadE9pGD seventhShS.flat wGoctadE9pGT = true :=
  shortCheckPk_sound _ 10 27 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wGoctadE9pW_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE9pG)
    (generatedAxisGlobalTwelveRepresentative 6)) = wGoctadE9pW.real := by
  have hT := (tensorPlanF_actual wGoctadE9pGPlan wGoctadE9pGPlan_ok (srcSeventhX0F_bnd (w := 64)
      (by norm_num))
    (by rw [wGoctadE9pGPlan_word, wGoctadE9pG_growth]; norm_num) srcSeventhD0).2
  rw [wGoctadE9pGPlan_word] at hT
  exact IdentVec.word_actual (seventhSrcVecS 64) wGoctadE9pGW wGoctadE9pG_check wGoctadE9pGD
      wGoctadE9pD_ok.2 wGoctadE9pGD_cols
    wGoctadE9pGD_rows wGoctadE9pGT wGoctadE9pGT_check _ hT _ (seventhSrcS_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
