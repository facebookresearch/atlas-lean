/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c18pChecksL

/-! # Factory checks (target side) of the identification Fourth[13]- <-> Seventh[27]+ (record
gforest:S7c18+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGforestS7c18pG_check : wGforestS7c18pGW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGforestS7c18pGD_cols : ∀ i : Fin 24, qmWordP (wGforestS7c18pGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGforestS7c18pGD.colsP i.val, wGforestS7c18pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGforestS7c18pGD_rows : ∀ i : Fin 24,
    fld 24 wGforestS7c18pGD.rowsP i.val = rowsOf (fun j => fld 24 wGforestS7c18pGD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGforestS7c18pGT_check : shortCheckF wGforestS7c18pGD fourthSrcShort.flat wGforestS7c18pGT
    = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wGforestS7c18pW_actual : griessConwayEncode (rhoLocal (identWordLocal wGforestS7c18pG)
    (generatedAxisGlobalTwelveRepresentative 3)) = wGforestS7c18pW.real := by
  have hT := (tensorPlanF_actual wGforestS7c18pGPlan wGforestS7c18pGPlan_ok (fourthSrcXW_bnd (w :=
      64) (by norm_num))
    (by rw [wGforestS7c18pGPlan_word, wGforestS7c18pG_growth]; norm_num) 1).2
  rw [wGforestS7c18pGPlan_word] at hT
  exact IdentVec.word_actual (fourthSrcVecW 64) wGforestS7c18pGW wGforestS7c18pG_check
      wGforestS7c18pGD wGforestS7c18pD_ok.2 wGforestS7c18pGD_cols
    wGforestS7c18pGD_rows wGforestS7c18pGT wGforestS7c18pGT_check _ hT _ (fourthSrcW_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
