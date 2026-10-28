/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c2pChecksL

/-! # Factory checks (target side) of the identification Fourth[18]- <-> Sixth[3]+ (record
gforest:S6c2+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGforestS6c2pG_check : wGforestS6c2pGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGforestS6c2pGD_cols : ∀ i : Fin 24, qmWordP (wGforestS6c2pGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS6c2pGD.colsP i.val, wGforestS6c2pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGforestS6c2pGD_rows : ∀ i : Fin 24,
    fld 24 wGforestS6c2pGD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS6c2pGD.colsP j.val) i :=
        by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGforestS6c2pGT_check : shortCheckF wGforestS6c2pGD fourthSrcShort.flat wGforestS6c2pGT =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wGforestS6c2pW_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS6c2pG)
    (generatedAxisGlobalTwelveRepresentative 3)) = wGforestS6c2pW.real := by
  have hT := (tensorPlanF_actual wGforestS6c2pGPlan wGforestS6c2pGPlan_ok (fourthSrcXW_bnd (w :=
      64) (by norm_num))
    (by rw [wGforestS6c2pGPlan_word, wGforestS6c2pG_growth]; norm_num) 1).2
  rw [wGforestS6c2pGPlan_word] at hT
  exact IdentVec.word_actual (fourthSrcVecW 64) wGforestS6c2pGW wGforestS6c2pG_check
      wGforestS6c2pGD wGforestS6c2pD_ok.2 wGforestS6c2pGD_cols
    wGforestS6c2pGD_rows wGforestS6c2pGT wGforestS6c2pGT_check _ hT _ (fourthSrcW_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
