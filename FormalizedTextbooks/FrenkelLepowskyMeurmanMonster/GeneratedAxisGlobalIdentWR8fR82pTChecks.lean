/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82pTChecksL

/-! # Factory checks (target side) of the identification Eighth[18]- <-> Root8[2]+ (record
r8f:R82+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wR8fR82pTG_check : wR8fR82pTGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wR8fR82pTGD_cols : ∀ i : Fin 24, qmWordP (wR8fR82pTGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR82pTGD.colsP i.val, wR8fR82pTGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wR8fR82pTGD_rows : ∀ i : Fin 24,
    fld 24 wR8fR82pTGD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR82pTGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wR8fR82pTGT_check : shortCheckF wR8fR82pTGD eighthShS.flat wR8fR82pTGT = true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wR8fR82pTW_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR82pTG)
    (generatedAxisGlobalTwelveRepresentative 7)) = wR8fR82pTW.real := by
  have hT := (tensorPlanF_actual wR8fR82pTGPlan wR8fR82pTGPlan_ok (eighthSrcXT_bnd (w := 64) (by
      norm_num))
    (by rw [wR8fR82pTGPlan_word, wR8fR82pTG_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH
        : ℚ) * 1))).2
  rw [wR8fR82pTGPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 64) wR8fR82pTGW wR8fR82pTG_check wR8fR82pTGD
      wR8fR82pTD_ok.2 wR8fR82pTGD_cols
    wR8fR82pTGD_rows wR8fR82pTGT wR8fR82pTGT_check _ hT _ (eighthSrcT_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
