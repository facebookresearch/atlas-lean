/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12pChecksL

/-! # Factory checks (target side) of the identification Root8[10]- <-> Seventh[19]+ (record
gforest:S7c12+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGforestS7c12pG_check : wGforestS7c12pGW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGforestS7c12pGD_cols : ∀ i : Fin 24, qmWordP (wGforestS7c12pGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS7c12pGD.colsP i.val, wGforestS7c12pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGforestS7c12pGD_rows : ∀ i : Fin 24,
    fld 24 wGforestS7c12pGD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS7c12pGD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGforestS7c12pGT_check : shortCheckF wGforestS7c12pGD srcRootEightCShort.flat
    wGforestS7c12pGT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wGforestS7c12pW_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS7c12pG)
    (generatedAxisGlobalTwelveRepresentative 9)) = wGforestS7c12pW.real := by
  have hT := (tensorPlanF_actual wGforestS7c12pGPlan wGforestS7c12pGPlan_ok (rootEightSrcXL_bnd (w
      := 64) (by norm_num))
    (by rw [wGforestS7c12pGPlan_word, wGforestS7c12pG_growth]; norm_num) 32).2
  rw [wGforestS7c12pGPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) wGforestS7c12pGW wGforestS7c12pG_check
      wGforestS7c12pGD wGforestS7c12pD_ok.2 wGforestS7c12pGD_cols
    wGforestS7c12pGD_rows wGforestS7c12pGT wGforestS7c12pGT_check _ hT _ (rootEightSrcL_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
