/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN7nXChecksL

/-! # Factory checks (target side) of the identification Fifth[4]+ <-> Ninth[12]- (record
gninth:N7-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGninthN7nXG_check : wGninthN7nXGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGninthN7nXGD_cols : ∀ i : Fin 24, qmWordP (wGninthN7nXGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN7nXGD.colsP i.val, wGninthN7nXGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGninthN7nXGD_rows : ∀ i : Fin 24,
    fld 24 wGninthN7nXGD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN7nXGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wGninthN7nXGT_check : shortCheckF wGninthN7nXGD fifthSrcShort.flat wGninthN7nXGT = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wGninthN7nXW_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN7nXG)
    (generatedAxisGlobalTwelveRepresentative 4)) = wGninthN7nXW.real := by
  have hT := (tensorPlanF_actual wGninthN7nXGPlan wGninthN7nXGPlan_ok (fifthSrcXW_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN7nXGPlan_word, wGninthN7nXG_growth]; norm_num) 1).2
  rw [wGninthN7nXGPlan_word] at hT
  exact IdentVec.word_actual (fifthSrcVecW 64) wGninthN7nXGW wGninthN7nXG_check wGninthN7nXGD
      wGninthN7nXD_ok.2 wGninthN7nXGD_cols
    wGninthN7nXGD_rows wGninthN7nXGT wGninthN7nXGT_check _ hT _ (fifthSrcW_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
