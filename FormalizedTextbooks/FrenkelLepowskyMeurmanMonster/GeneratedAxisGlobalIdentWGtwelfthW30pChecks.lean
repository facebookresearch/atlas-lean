/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30pChecksL

/-! # Factory checks (target side) of the identification Twelfth[30]- <-> Twelfth[30]+ (record
gtwelfth:W30+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGtwelfthW30pG_check : wGtwelfthW30pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGtwelfthW30pGD_cols : ∀ i : Fin 24, qmWordP (wGtwelfthW30pGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGtwelfthW30pGD.colsP i.val, wGtwelfthW30pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGtwelfthW30pGD_rows : ∀ i : Fin 24,
    fld 24 wGtwelfthW30pGD.rowsP i.val = rowsOf (fun j => fld 24 wGtwelfthW30pGD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGtwelfthW30pGT_check : shortCheckF wGtwelfthW30pGD twelfthShS.flat wGtwelfthW30pGT = true
    :=
  shortCheckPk_sound _ 10 46 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wGtwelfthW30pW_actual : griessConwayEncode (rhoLocal (identWordLocal wGtwelfthW30pG)
    (generatedAxisGlobalTwelveRepresentative 10)) = wGtwelfthW30pW.real := by
  have hT := (tensorPlanF_actual wGtwelfthW30pGPlan wGtwelfthW30pGPlan_ok (twelfthSrcXW_bnd (w :=
      64) (by norm_num))
    (by rw [wGtwelfthW30pGPlan_word, wGtwelfthW30pG_growth]; norm_num) 32).2
  rw [wGtwelfthW30pGPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) wGtwelfthW30pGW wGtwelfthW30pG_check
      wGtwelfthW30pGD wGtwelfthW30pD_ok.2 wGtwelfthW30pGD_cols
    wGtwelfthW30pGD_rows wGtwelfthW30pGT wGtwelfthW30pGT_check _ hT _ (twelfthSrcS_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
