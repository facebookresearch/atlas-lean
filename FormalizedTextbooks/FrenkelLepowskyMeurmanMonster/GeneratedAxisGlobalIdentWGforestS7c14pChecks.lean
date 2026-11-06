/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14pChecksL

/-! # Factory checks (target side) of the identification Eighth[27]+ <-> Seventh[22]+ (record
gforest:S7c14+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGforestS7c14pG_check : wGforestS7c14pGW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGforestS7c14pGD_cols : ∀ i : Fin 24, qmWordP (wGforestS7c14pGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS7c14pGD.colsP i.val, wGforestS7c14pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGforestS7c14pGD_rows : ∀ i : Fin 24,
    fld 24 wGforestS7c14pGD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS7c14pGD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGforestS7c14pGT_check : shortCheckF wGforestS7c14pGD eighthShS.flat wGforestS7c14pGT =
    true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wGforestS7c14pW_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS7c14pG)
    (generatedAxisGlobalTwelveRepresentative 7)) = wGforestS7c14pW.real := by
  have hT := (tensorPlanF_actual wGforestS7c14pGPlan wGforestS7c14pGPlan_ok (eighthSrcXT_bnd (w :=
      64) (by norm_num))
    (by rw [wGforestS7c14pGPlan_word, wGforestS7c14pG_growth]; norm_num) (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1))).2
  rw [wGforestS7c14pGPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 64) wGforestS7c14pGW wGforestS7c14pG_check
      wGforestS7c14pGD wGforestS7c14pD_ok.2 wGforestS7c14pGD_cols
    wGforestS7c14pGD_rows wGforestS7c14pGT wGforestS7c14pGT_check _ hT _ (eighthSrcT_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
