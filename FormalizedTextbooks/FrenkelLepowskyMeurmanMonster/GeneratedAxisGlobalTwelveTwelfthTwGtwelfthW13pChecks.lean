/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pChecksL

/-! # Factory checks (target side) of the identification Twelfth[13]- <-> Twelfth[13]+ (record
gtwelfth:W13+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem twGtwelfthW13pG_check : twGtwelfthW13pGW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem twGtwelfthW13pGD_cols : ∀ i : Fin 24, qmWordP (twGtwelfthW13pGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 twGtwelfthW13pGD.colsP i.val, twGtwelfthW13pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem twGtwelfthW13pGD_rows : ∀ i : Fin 24,
    fld 24 twGtwelfthW13pGD.rowsP i.val = rowsOf (fun j => fld 24 twGtwelfthW13pGD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem twGtwelfthW13pGT_check0 :
    shortCheckPk twGtwelfthW13pGD 10 15 ((twelfthShS.flat).take 15360) ((twGtwelfthW13pGT).take
        15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem twGtwelfthW13pGT_check1 :
    shortCheckPk twGtwelfthW13pGD 10 15 (((twelfthShS.flat).drop 15360).take 15360)
        (((twGtwelfthW13pGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem twGtwelfthW13pGT_check2 :
    shortCheckPk twGtwelfthW13pGD 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360)
        ((((twGtwelfthW13pGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem twGtwelfthW13pGT_check3 :
    shortCheckPk twGtwelfthW13pGD 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360)
        ((((twGtwelfthW13pGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem twGtwelfthW13pGT_check : shortCheckF twGtwelfthW13pGD twelfthShS.flat twGtwelfthW13pGT =
    true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW13pGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW13pGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ twGtwelfthW13pGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ twGtwelfthW13pGT_check3)))

/-- The coordinates of the target image. -/
theorem twGtwelfthW13pW_actual : griessConwayEncode (rhoLocal (identWordLocal twGtwelfthW13pG)
    (generatedAxisGlobalTwelveRepresentative 10)) = twGtwelfthW13pW.real := by
  have hT := (tensorPlanF_actual twGtwelfthW13pGPlan twGtwelfthW13pGPlan_ok (twelfthSrcXW_bnd (w
      := 80) (by norm_num))
    (by rw [twGtwelfthW13pGPlan_word, twGtwelfthW13pG_growth]; norm_num) 32).2
  rw [twGtwelfthW13pGPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 80) twGtwelfthW13pGW twGtwelfthW13pG_check
      twGtwelfthW13pGD twGtwelfthW13pD_ok.2 twGtwelfthW13pGD_cols
    twGtwelfthW13pGD_rows twGtwelfthW13pGT twGtwelfthW13pGT_check _ hT _ (twelfthSrcS_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
