/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nChecksL

/-! # Factory checks (target side) of the identification Eighth[13]+ <-> Seventh[14]- (record
gforest:S7c8-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGforestS7c8nG_check : wGforestS7c8nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGforestS7c8nGD_cols : ∀ i : Fin 24, qmWordP (wGforestS7c8nGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS7c8nGD.colsP i.val, wGforestS7c8nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGforestS7c8nGD_rows : ∀ i : Fin 24,
    fld 24 wGforestS7c8nGD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS7c8nGD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGforestS7c8nGT_check : shortCheckF wGforestS7c8nGD eighthShS.flat wGforestS7c8nGT = true :=
  shortCheckPk_sound _ 10 43 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wGforestS7c8nW_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS7c8nG)
    (generatedAxisGlobalTwelveRepresentative 7)) = wGforestS7c8nW.real := by
  have hT := (tensorPlanF_actual wGforestS7c8nGPlan wGforestS7c8nGPlan_ok (eighthSrcXT_bnd (w :=
      72) (by norm_num))
    (by rw [wGforestS7c8nGPlan_word, wGforestS7c8nG_growth]; norm_num) (2 * ((tensorWordDenAll
        srcEighthH : ℚ) * 1))).2
  rw [wGforestS7c8nGPlan_word] at hT
  exact IdentVec.word_actual (eighthSrcVecT 72) wGforestS7c8nGW wGforestS7c8nG_check
      wGforestS7c8nGD wGforestS7c8nD_ok.2 wGforestS7c8nGD_cols
    wGforestS7c8nGD_rows wGforestS7c8nGT wGforestS7c8nGT_check _ hT _ (eighthSrcT_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
